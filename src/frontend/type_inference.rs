use super::error::{FrontEndError, LastLayerError};
/// Type inference module, uses Hindley-Milner type inference algorithm.
/// Type inference consists of two main steps. First, it collects the types
/// from all modules for global namespace (global functions, constants and type declarations)
/// Then it performs type inference for each module.
///
/// Keep it mind that the type inference is somewhat fuzzy, if you write a function
/// `def foo(): Bar = zoo()`, it does not check that he type `Bar` is actually
/// a type. It just checks that zoo returns the type with the same name (additionaly,
/// if the two types had generics, it would check that the generics are the same).
///
/// The main structure used is the Type structure, which is a constructor with a name
/// and arguments (Int[], Float[], Result[T1, T2], etc.). When it has arguments,
/// those can either be types or type variables, when the types are not yet known
/// in the inference.
// TODO: Check if the Rcs are truly necessary.
use super::utils::{GenericDeclaration, IdEnv, StronglyTypedIdentifier, WrittenType};
use crate::ast::{
    Decl, DeclKind, Expr, ExprKind, FunDecl, Module, Operator, Pattern, Stmt, StmtKind, VarDecl,
};
use crate::backend::ast_interpreter::native_functions::get_native_functions;
use crate::constants::STD_NATIVE_MODULE;
use crate::location::Location;
use log::debug;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum ErrorKind {
    TypeMismatch,
    UnificationError,
    /// When a type is expected, but none is found.
    TypeExpected,
}

type TypeInferenceError = FrontEndError<ErrorKind>;

/// Generate new typevar
fn new_typevar() -> Type {
    static mut COUNTER: usize = 0;
    // TODO: Get rid of this unsafe piece of a guy
    Type::TypeVar(TypeVar(unsafe {
        COUNTER += 1;
        COUNTER
    }))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVar(usize);

/// Constructors are the types that are defined in the source code. For example, Int, List<T>,
/// Either<L, R>, etc. Also, functions are represented via constructors. Function<ReturnType,
/// Args...> Constructor name can be a type variable, so we can represent generic types.
#[derive(Debug, Clone)]
pub struct Constructor<T> {
    pub name: String,
    pub type_vec: Vec<Rc<T>>,
}

#[derive(Debug, Clone)]
pub enum Type {
    TypeVar(TypeVar),
    Constructor(Constructor<Type>),
}

/// Used for types which are not yet instantiated. For example function declarations with generics,
/// where it is not known what the actual types will be, and they will be different for each
/// function call.
#[derive(Debug, Clone)]
pub struct TypeScheme {
    pub generics: Vec<GenericDeclaration>,
    pub ty: Rc<Type>,
}

impl<T: std::fmt::Display> Display for Constructor<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        if self.type_vec.is_empty() {
            return Ok(());
        }

        write!(f, "[")?;
        for (i, t) in self.type_vec.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", t)?;
        }
        write!(f, "]")
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::TypeVar(TypeVar(id)) => write!(f, "?T{}", id),
            Type::Constructor(cons) => write!(f, "{}", cons),
        }
    }
}

impl TypeScheme {
    pub fn create_function(generics: Vec<GenericDeclaration>, ty: Rc<Type>) -> Self {
        Self { generics, ty }
    }

    /// Returns a type where all generic parameters were replaced by
    /// fresh type variable.
    fn instantiate(&self) -> Result<Rc<Type>, TypeInferenceError> {
        let generic_map = self
            .generics
            .iter()
            .map(|g| (g.name.clone(), new_typevar().into_rc()))
            .collect::<HashMap<String, Rc<Type>>>();
        self.ty.clone().fill_types(&generic_map)
    }
}

impl Constructor<Type> {
    fn fill_types(&self, map: &HashMap<String, Rc<Type>>) -> Result<Rc<Type>, TypeInferenceError> {
        if let Some(t) = map.get(&self.name) {
            if self.type_vec.is_empty() {
                Ok(t.clone())
            } else {
                Err(TypeInferenceError::new(
                    ErrorKind::UnificationError,
                    // TODO: Location
                    Location::new(0, 0),
                    "Cannot replace type variable with a constructor that has generics".to_string(),
                ))
            }
        } else {
            let type_vec = self
                .type_vec
                .iter()
                .map(|t| t.fill_types(map))
                .collect::<Result<_, _>>()?;
            Ok(Type::Constructor(Constructor {
                name: self.name.clone(),
                type_vec,
            })
            .into_rc())
        }
    }
}

impl Type {
    pub fn is_typevar(&self) -> bool {
        matches!(self, Type::TypeVar(_))
    }

    pub fn into_rc(self) -> Rc<Type> {
        Rc::new(self)
    }

    pub fn create_constant(name: String) -> Rc<Type> {
        Type::Constructor(Constructor {
            name,
            type_vec: vec![],
        })
        .into_rc()
    }

    /// Converts this type into TypeScheme without any generics
    pub fn into_scheme(self) -> TypeScheme {
        TypeScheme {
            generics: vec![],
            ty: self.into_rc(),
        }
    }

    /// Function is represented as a constructor Function<ReturnType, ...Args>
    pub fn create_function(mut parameters: Vec<Rc<Type>>, return_type: Rc<Type>) -> Type {
        parameters.insert(0, return_type);
        Type::Constructor(Constructor {
            name: "Function".to_string(),
            type_vec: parameters,
        })
    }

    /// Creates a new type where every occurence of each variable in map is replaced.
    /// This is mainly targeted for filling generic variables. For example:
    /// (T<Q>, { T -> Int }) => Int<Q>
    ///
    /// If the type is a constructor with parameters which name matches the name in map, the
    /// replacement cannot be performed and error will be returned. (T<Q>, { T -> CustomType }) =>
    /// CustomType<Q> will result in an error.
    pub fn fill_types(
        &self,
        map: &HashMap<String, Rc<Type>>,
    ) -> Result<Rc<Type>, TypeInferenceError> {
        match self {
            Type::TypeVar(_) => Ok(self.clone().into_rc()),
            Type::Constructor(cons) => cons.fill_types(map),
        }
    }
}

impl WrittenType {
    fn into_type(self) -> Type {
        match self {
            WrittenType::Identifier { name, generics } => Type::Constructor(Constructor {
                name,
                type_vec: generics
                    .into_iter()
                    .map(|g| Rc::new(g.into_type()))
                    .collect(),
            }),
            WrittenType::Function {
                params,
                return_type,
            } => {
                let params = params
                    .into_iter()
                    .map(|p| p.into_type().into_rc())
                    .collect::<Vec<_>>();
                let return_type = return_type.into_type();
                Type::create_function(params, return_type.into_rc())
            }
        }
    }

    fn as_cloned_type(&self) -> Rc<Type> {
        self.clone().into_type().into_rc()
    }
}

#[derive(Debug, Clone)]
struct StructMetadata {
    generics: Vec<String>,
    fields: HashMap<String, Type>,
    methods: HashMap<String, TypeScheme>,
}

impl StructMetadata {
    // struct_type should be the constructor representing the struct, having in its type_vec its
    // instantiated generics.
    fn instantiate_struct(
        &self,
        struct_type: &Constructor<Type>,
    ) -> Result<HashMap<String, Rc<Type>>, TypeInferenceError> {
        assert!(self.generics.len() == struct_type.type_vec.len());
        let map = self
            .generics
            .iter()
            .zip(struct_type.type_vec.iter())
            .map(|(g, t)| (g.clone(), t.clone()))
            .collect::<HashMap<_, _>>();

        let mut fields = HashMap::new();
        for (name, ty) in self.fields.iter() {
            fields.insert(name.clone(), ty.fill_types(&map)?);
        }

        Ok(fields)
    }
}

/// Holds the metadata of a type, for example the fields and generics of a struct.
/// Does not hold a name, expected to be stored in the symbol table.
#[derive(Debug, Clone)]
enum TypeMetadata {
    Struct(StructMetadata),
    /// Enum variants are represented as functions, here we store the names of those functions.
    /// This is mainly used for imports (the user only imports the enum types, not the variants)
    /// so that we know what functions to export.
    Enum {
        variant_names: Vec<String>,
        methods: HashMap<String, TypeScheme>,
        generics: Vec<String>,
    },
}

/// Semi-typed module. Mainly items that can be used across modules, like types and functions.
#[derive(Debug, Clone)]
struct ModuleMetadata {
    types: HashMap<String, TypeMetadata>,
    /// The symbol table for symbols which are not types (functions, variables, etc.)
    ids: HashMap<String, TypeScheme>,
}

pub struct SymbolTable {
    /// A table of type variables and their corresponding types.
    unif_table: HashMap<TypeVar, Rc<Type>>,
    ids: IdEnv<TypeScheme>,
    type_ids: HashMap<String, TypeMetadata>,
}

impl SymbolTable {
    fn unify(
        &mut self,
        t1: &Rc<Type>,
        t2: &Rc<Type>,
        location: Location,
    ) -> Result<(), TypeInferenceError> {
        debug!("Unifying ⟦{}⟧ = ⟦{}⟧", t1, t2);
        match (t1.as_ref(), t2.as_ref()) {
            // This is a quick fix, some programs would cause an unification of T?1 = T?1,
            // which would cause an infinite loop.
            (Type::TypeVar(x), Type::TypeVar(y)) if x == y => {}
            (Type::TypeVar(tv), _) => {
                let t = self.unif_table.get(tv);
                if let Some(t) = t {
                    debug!("Unifying type {} variable with type {}", t, t2);
                    self.unify(&t.clone(), t2, location)?;
                }

                self.unif_table.insert(*tv, t2.clone());
            }
            (_, Type::TypeVar(tv)) => {
                let t = self.unif_table.get(tv);
                if let Some(t) = t {
                    self.unify(&t.clone(), t1, location)?;
                }

                self.unif_table.insert(*tv, t1.clone());
            }
            (Type::Constructor(c1), Type::Constructor(c2)) if c1.name == c2.name => {
                for (t1, t2) in c1.type_vec.iter().zip(c2.type_vec.iter()) {
                    self.unify(t1, t2, location)?;
                }
            }
            _ => {
                return Err(TypeInferenceError::new(
                    ErrorKind::UnificationError,
                    location,
                    format!(
                        "Type inference error, cannot unify type '{}' with type '{}'",
                        t1, t2,
                    ),
                ));
            }
        }
        Ok(())
    }

    fn new(ids: HashMap<String, TypeScheme>, type_ids: HashMap<String, TypeMetadata>) -> Self {
        Self {
            unif_table: HashMap::new(),
            ids: IdEnv::new_with_init(ids),
            type_ids,
        }
    }

    /// Performs type inference upon the function body and returns the inferred type of the
    /// function. Does not store the function into the symbol table.
    /// It will also mutate the inferred_* fields of the FunDecl (it'll fill them).
    fn visit_function(
        &mut self,
        FunDecl {
            name,
            parameters,
            inferred_parameters,
            return_type,
            inferred_return_type,
            body,
            ..
        }: &mut FunDecl,
    ) -> Result<Type, TypeInferenceError> {
        // TODO: Check if we don't do things twice (here and in the precollect step)
        debug!("Visiting function {}", name);
        self.ids.push();
        let mut typed_params = vec![];
        for param in parameters {
            let ty = param
                .ty
                .clone()
                .map(|ty| ty.into_type())
                .unwrap_or_else(new_typevar)
                .into_rc();
            self.ids
                .insert(param.name.clone(), (*ty).clone().into_scheme());
            typed_params.push(ty);
        }

        let ret_ty_stated = return_type
            .clone()
            .map(|ty| ty.into_type())
            .unwrap_or_else(new_typevar)
            .into_rc();

        let fun_ty = Type::create_function(typed_params.clone(), ret_ty_stated.clone());

        *inferred_return_type = Some(ret_ty_stated.clone());
        *inferred_parameters = Some(typed_params.clone());

        // Visiting the function body must be done at the
        // end, when we have all the types in the symbol table.
        // Otherwise, recursive functions will not work.
        let ret_ty = self.visit_expr(body)?;
        self.ids.pop();

        // TODO: Missing location here
        self.unify(&ret_ty_stated, &ret_ty, Location::new(0, 0))?;

        Ok(fun_ty.clone())
    }

    fn visit_method(
        &mut self,
        target_type: Rc<Type>,
        method: &mut FunDecl,
    ) -> Result<(), TypeInferenceError> {
        self.ids.push();
        self.ids
            .insert("self".to_string(), (*target_type).clone().into_scheme());
        self.visit_function(method)?;
        self.ids.pop();
        Ok(())
    }

    fn visit_decl(&mut self, decl: &mut Decl) -> Result<(), TypeInferenceError> {
        match &mut decl.node {
            DeclKind::FunDecl(fun) => {
                let fun_ty = self.visit_function(fun)?;
                let fun_scheme =
                    TypeScheme::create_function(fun.generics.clone(), fun_ty.clone().into_rc());

                debug!("Adding function {} with type {}", fun.name, fun_ty);
                self.ids.insert(fun.name.clone(), fun_scheme);

                decl.inferred_ty = Some(fun_ty);
            }
            DeclKind::EnumDecl {
                name,
                variants,
                generics,
                methods,
            } => {
                // The return type of the variant constructors. This needn't be a type scheme
                // since the functions will be type schemes.
                let enum_ty = Type::Constructor(Constructor {
                    name: name.clone(),
                    type_vec: generics
                        .iter()
                        .map(|g| Type::create_constant(g.name.clone()))
                        .collect(),
                })
                .into_rc();

                // TODO: Shouldn't this be done in the precollect step?
                // Add the variants as function types
                for variant in variants {
                    let fields: Vec<Rc<Type>> = variant
                        .fields
                        .clone()
                        .into_iter()
                        .map(|field| field.into_type().into_rc())
                        .collect();
                    let fun_ty = TypeScheme {
                        ty: Type::create_function(fields.clone(), enum_ty.clone()).into_rc(),
                        generics: generics.clone(),
                    };
                    self.ids.insert(variant.name.clone(), fun_ty);
                }

                for method in methods {
                    self.visit_method(enum_ty.clone(), method)?;
                }
            }
            DeclKind::StructDecl {
                name,
                methods,
                generics,
                ..
            } => {
                let type_ = Type::Constructor(Constructor {
                    name: name.clone(),
                    type_vec: generics
                        .iter()
                        .map(|g| Type::create_constant(g.name.clone()))
                        .collect(),
                })
                .into_rc();
                for method in methods {
                    self.visit_method(type_.clone(), method)?;
                }
            }
            DeclKind::ImplDecl { .. } => {
                unreachable!("This should have been already removed")
            }
            _ => todo!(),
        }
        Ok(())
    }

    fn visit_stmt(&mut self, stmt: &mut Stmt) -> Result<(), TypeInferenceError> {
        match &mut stmt.node {
            StmtKind::VarDecl(VarDecl {
                name,
                ty,
                value,
                inferred_ty,
            }) => {
                let var_ty = match ty {
                    Some(ty) => ty.as_cloned_type(),
                    None => new_typevar().into_rc(),
                };
                let scheme = (*var_ty).clone().into_scheme();
                self.ids.insert(name.clone(), scheme.clone());
                *inferred_ty = Some((*scheme.ty).clone());
                let value_ty = self.visit_expr(value)?;
                self.unify(&var_ty, &value_ty, stmt.location)?;
            }
            StmtKind::Expr(expr) => {
                self.visit_expr(expr)?;
            }
        }
        Ok(())
    }

    fn visit_expr(&mut self, expr: &mut Expr) -> Result<Rc<Type>, TypeInferenceError> {
        let res = match &mut expr.node {
            ExprKind::Unit => Ok(Type::create_constant("Unit".to_string())),
            ExprKind::Int(_) => Ok(Type::create_constant("Int".to_string())),
            ExprKind::Boolean(_) => Ok(Type::create_constant("Bool".to_string())),
            ExprKind::Char(_) => Ok(Type::create_constant("Char".to_string())),
            ExprKind::Identifier(id) => {
                let ty = match self.ids.get(id) {
                    Some(ty) => ty.instantiate()?,
                    None => Err(TypeInferenceError::new(
                        ErrorKind::TypeMismatch,
                        expr.location,
                        format!("Type {} not found", id),
                    ))?,
                };
                Ok(ty)
            }
            ExprKind::Compound(stmts, ret) => {
                self.ids.push();
                for stmt in stmts {
                    self.visit_stmt(stmt)?;
                }
                let ret = self.visit_expr(ret);
                self.ids.pop();
                ret
            }
            ExprKind::FunCall { target, args } => {
                let target_type = self.visit_expr(target)?;
                let arg_types = args
                    .iter_mut()
                    .map(|arg| self.visit_expr(arg))
                    .collect::<Result<_, _>>()?;
                let ret_ty = new_typevar().into_rc();
                let fun_ty = Type::create_function(arg_types, ret_ty.clone()).into_rc();

                self.unify(&target_type, &fun_ty, expr.location)?;

                Ok(ret_ty)
            }
            ExprKind::If { cond, then, els } => {
                let cond_ty = self.visit_expr(cond)?;
                let then_ty = self.visit_expr(then)?;
                let else_ty = self.visit_expr(els)?;

                self.unify(
                    &cond_ty,
                    &Type::create_constant("Bool".to_string()),
                    expr.location,
                )?;

                self.unify(&then_ty, &else_ty, expr.location)?;

                Ok(then_ty)
            }
            ExprKind::Binary { op, lhs, rhs, .. } => {
                // TODO: The types must be the same and, if the operator is a
                // comparison operator, the result must be a bool.
                let lhs_ty = self.visit_expr(lhs)?;
                let rhs_ty = self.visit_expr(rhs)?;
                self.unify(&lhs_ty, &rhs_ty, expr.location)?;

                match op {
                    Operator::Less
                    | Operator::Greater
                    | Operator::LessEqual
                    | Operator::GreaterEqual
                    | Operator::Equal
                    | Operator::Neq => Ok(Type::create_constant("Bool".to_string())),
                    _ => Ok(lhs_ty),
                }
            }
            ExprKind::Match { target, arms } => {
                let target_ty = self.visit_expr(target)?;

                let ret_ty = new_typevar().into_rc();
                for arm in arms {
                    self.ids.push();
                    debug!(
                        "Unifying pattern `{}` with target type `{}`",
                        arm.pattern, target_ty
                    );

                    self.unify_pattern(&arm.pattern, &target_ty, target.location)?;

                    if let Some(arm_cond) = arm.cond.as_mut() {
                        let ty = self.visit_expr(arm_cond)?;
                        debug!("Unifying condition with type {}", ty);
                        self.unify(
                            &ty,
                            &Type::create_constant("Bool".to_string()),
                            expr.location,
                        )?;
                    }

                    let arm_ty = self.visit_expr(&mut arm.body)?;
                    self.unify(&ret_ty, &arm_ty, expr.location)?;
                    self.ids.pop();
                }
                Ok(ret_ty)
            }
            ExprKind::StructInitializer {
                name,
                generics,
                fields,
            } => {
                // TODO: The inference does not really do anything at this point, we would
                // like the following:
                // ```
                // StructFoo<T> { x: T };
                // let x = StructFoo { x: 1 };
                //
                // // instead of
                //
                // let x = StructFoo<Int> { x: 1 };
                // ```
                let type_vec = generics
                    .iter()
                    .map(|g| g.clone().into_type().into_rc())
                    .collect();

                let struct_type = Constructor {
                    name: name.clone(),
                    type_vec,
                };

                let struct_metadata = match self.type_ids.get(name) {
                    Some(TypeMetadata::Struct(metadata)) => metadata.clone(), // clone for borrow
                    // checker
                    _ => {
                        return Err(TypeInferenceError::new(
                            ErrorKind::TypeMismatch,
                            expr.location,
                            format!("Struct {} not found; name used as struct initializer", name),
                        ));
                    }
                };

                let fields_typed = struct_metadata.instantiate_struct(&struct_type)?;

                // Check that the field initializers have correct types.
                for (field_name, field_expr) in fields {
                    let field_ty = match fields_typed.get(field_name) {
                        Some(ty) => ty,
                        None => {
                            return Err(TypeInferenceError::new(
                                ErrorKind::TypeMismatch,
                                expr.location,
                                format!("Field {} not found in struct {}", field_name, name),
                            ));
                        }
                    };

                    let expr_ty = self.visit_expr(field_expr)?;
                    self.unify(&expr_ty, field_ty, expr.location)?;
                }

                Ok(Type::Constructor(struct_type).into_rc())
            }
            ExprKind::MemberAccess { target, member } => {
                let ty = self.visit_expr(target)?;

                let closed_ty = self.close_type(&ty)?;
                let cons = match closed_ty.as_ref() {
                    Type::Constructor(cons) => cons,
                    _ => {
                        return Err(TypeInferenceError::new(
                            ErrorKind::TypeMismatch,
                            expr.location,
                            "The type of the struct must be known at this point".to_string(),
                        ));
                    }
                };

                // Try to extract the member as a field or a method
                let (members, methods, generics) = match self.type_ids.get(&cons.name) {
                    Some(TypeMetadata::Struct(StructMetadata {
                        generics,
                        fields,
                        methods,
                    })) => (fields, methods, generics),
                    Some(TypeMetadata::Enum {
                        methods, generics, ..
                    }) => (&HashMap::new(), methods, generics),
                    _ => {
                        return Err(TypeInferenceError::new(
                            ErrorKind::TypeMismatch,
                            expr.location,
                            format!(
                                "Target type {} not found when accessing member {}",
                                cons.name, member
                            ),
                        ));
                    }
                };

                let member_type = if let Some(ty) = members.get(member) {
                    ty.clone().into_rc()
                } else if let Some(ty) = methods.get(member) {
                    ty.instantiate()?
                } else {
                    return Err(TypeInferenceError::new(
                        ErrorKind::TypeMismatch,
                        expr.location,
                        format!("Member {} not found in struct {}", member, cons.name),
                    ));
                };

                let types = generics.iter().zip(cons.type_vec.iter()).fold(
                    HashMap::new(),
                    |mut map, (g, t)| {
                        map.insert(g.clone(), t.clone());
                        map
                    },
                );
                member_type.fill_types(&types)
            }
            ExprKind::Lambda(fun) => Ok(self.visit_function(fun)?.into_rc()),
        }?;
        expr.inferred_ty = Some(res.clone());
        Ok(res)
    }

    /// Collects types from an imported module into the current symbol table.
    /// Returns the symbol table with the imported types.
    fn collect_from_import(&mut self, imported_ids: &[&str], imported_module: &ModuleMetadata) {
        debug!("Collecting from import: {}", imported_ids.join(", "));
        for id in imported_ids {
            // For functions
            if let Some(ty) = imported_module.ids.get(*id) {
                self.ids.insert(id.to_string(), ty.clone());
                // Others (structs, enums)
            } else if let Some(ty) = imported_module.types.get(*id) {
                match ty {
                    TypeMetadata::Struct(metadata) => {
                        self.type_ids
                            .insert(id.to_string(), TypeMetadata::Struct(metadata.clone()));
                    }
                    TypeMetadata::Enum { variant_names, .. } => {
                        for variant in variant_names {
                            let cons = imported_module.ids.get(variant).expect("Inner compiler error; Couldn't find variant constructor which should be exported");
                            self.ids.insert(variant.clone(), cons.clone());
                        }
                        self.type_ids.insert(id.to_string(), ty.clone());
                    }
                }
            }
        }
    }

    fn unify_pattern(
        &mut self,
        pattern: &Pattern,
        target_ty: &Rc<Type>,
        location: Location,
    ) -> Result<(), TypeInferenceError> {
        match (pattern, target_ty.as_ref()) {
            (Pattern::Wildcard, _) => Ok(()),
            (Pattern::Int(_), _) => self.unify(
                target_ty,
                &Type::create_constant("Int".to_string()),
                location,
            ),
            (Pattern::Boolean(_), _) => self.unify(
                target_ty,
                &Type::create_constant("Bool".to_string()),
                location,
            ),
            (Pattern::String(_), _) => self.unify(
                target_ty,
                &Type::create_constant("String".to_string()),
                location,
            ),
            (Pattern::Struct { name, fields }, _) => {
                let struct_metadata = match self.type_ids.get(name) {
                    Some(TypeMetadata::Struct(metadata)) => metadata,
                    _ => {
                        return Err(TypeInferenceError::new(
                            ErrorKind::TypeMismatch,
                            location,
                            format!("Struct {} not found when matching patterns", name),
                        ));
                    }
                };

                let closed_target = self.close_type(target_ty)?;
                let c = match closed_target.as_ref() {
                    Type::Constructor(c) => c,
                    _ => {
                        return Err(TypeInferenceError::new(
                            ErrorKind::TypeMismatch,
                            location,
                            format!("Type must be known at this point: {}", target_ty),
                        ));
                    }
                };

                if c.name != *name {
                    return Err(TypeInferenceError::new(
                        ErrorKind::TypeMismatch,
                        location,
                        format!("Expected struct {}, got {}", name, c.name),
                    ));
                }

                let struct_type = struct_metadata.instantiate_struct(c)?;

                for field in fields.iter() {
                    let field_ty = match struct_type.get(field) {
                        Some(ty) => ty.as_ref().clone(),
                        None => {
                            return Err(TypeInferenceError::new(
                                ErrorKind::TypeMismatch,
                                location,
                                format!("Field {} not found in struct {}", field, name),
                            ));
                        }
                    };
                    self.ids.insert(field.clone(), field_ty.into_scheme());
                }
                Ok(())
            }
            (Pattern::Enum { name, patterns }, _) => {
                debug!("Unifying enum pattern {} with target {}", name, target_ty);
                // Constructing enum variant is done with a function call, with the same
                // name and parameters of the variant. To check the types, we will
                // use this function. First, we find it by name and instantiate it
                // by the generics, since the target of the pattern match is equal
                // to the return type of the constructor.
                let variant_cons = match self.ids.get(name) {
                    Some(cons) if cons.ty.is_typevar() => {
                        panic!("Compiler error; Enum constructor should be known at this point; cons: {:?}, pattern: {:?}, target: {:?}", cons, pattern, target_ty)
                    }
                    Some(cons) => Ok(cons),
                    None => Err(TypeInferenceError::new(
                        ErrorKind::TypeMismatch,
                        location,
                        format!("Enum constructor not found for {}", name),
                    )),
                }?;

                // The order of generics correspond to the order of the types in the return
                // constructor.
                // TODO: The type must be at least partially known at this point.
                // Consider if this requirement is necessary.
                let finalized_target = self.close_type(target_ty)?;
                let instantiated_generics = match finalized_target.as_ref() {
                    Type::Constructor(Constructor { type_vec, .. }) => type_vec,
                    _ => {
                        return Err(TypeInferenceError::new(
                            ErrorKind::TypeMismatch,
                            location,
                            format!("Type must be known at this point: {}", target_ty),
                        ));
                    }
                };

                // Generic name -> Actual type
                let generics: HashMap<String, Rc<Type>> = variant_cons
                    .generics
                    .iter()
                    .map(|g| g.name.clone())
                    .zip(instantiated_generics.iter().cloned())
                    .collect::<HashMap<_, _>>();

                let cons_inst = variant_cons.ty.fill_types(&generics)?;
                debug!(
                    "Instantiated enum variant pattern as constructor: {}",
                    cons_inst
                );

                // Now we have the type of the constructor,
                // we can check the types of the patterns
                let cons = match cons_inst.as_ref() {
                    Type::Constructor(cons) => cons,
                    _ => {
                        return Err(TypeInferenceError::new(
                            ErrorKind::TypeMismatch,
                            location,
                            format!("Expected enum variant instance, got {}", cons_inst),
                        ));
                    }
                };

                let params = cons.type_vec[1..].iter();
                for (pattern, ty) in patterns.iter().zip(params) {
                    self.unify_pattern(pattern, ty, location)?;
                }
                Ok(())
            }
            (Pattern::Identifier(name), ty) => {
                // `match self { None => ... }` is a special case.
                // The `None` is treated as a variant if the constructor
                // exists in scope. This is only considered if the
                // type of the pattern is already known constructor
                // with function type. TODO: This however should be fully
                // checked that this really is an enum cons.
                if let Some(cons) = self.ids.get(name) {
                    match cons.ty.as_ref() {
                        Type::Constructor(Constructor {
                            name: cons_name, ..
                        }) if cons_name == "Function" => {
                            return self.unify_pattern(
                                &Rc::new(Pattern::Enum {
                                    name: name.clone(),
                                    patterns: vec![],
                                }),
                                target_ty,
                                location,
                            );
                        }
                        _ => (),
                    }
                }
                self.ids.insert(name.clone(), (*ty).clone().into_scheme());
                Ok(())
            }
        }
    }

    /// Recursively replaces all type variables with the type they are unified with.
    /// If the type variable is not found in the unification table, an error is returned.
    fn close_type(&self, ty: &Rc<Type>) -> Result<Rc<Type>, TypeInferenceError> {
        match ty.as_ref() {
            Type::TypeVar(TypeVar(id)) => {
                let t = self.unif_table.get(&TypeVar(*id)).ok_or_else(|| {
                    panic!(
                        "Type variable {} not found in unification table, this should not happen",
                        id
                    )
                })?;
                self.close_type(t)
            }
            Type::Constructor(cons) => {
                let type_vec = cons
                    .type_vec
                    .iter()
                    .map(|t| self.close_type(t))
                    .collect::<Result<_, _>>()?;
                Ok(Type::Constructor(Constructor {
                    name: cons.name.clone(),
                    type_vec,
                })
                .into_rc())
            }
        }
    }

    fn finalize_fun(&mut self, fun_decl: FunDecl) -> Result<FunDecl, TypeInferenceError> {
        debug!("Finalizing function {}", fun_decl.name);
        let closed_params = fun_decl
            .inferred_parameters
            .expect("Finalize must be done after types are inferred")
            .into_iter()
            .map(|t| self.close_type(&t))
            .collect::<Result<Vec<_>, _>>()?;

        let closed_return_type = self.close_type(
            &fun_decl
                .inferred_return_type
                .expect("Finalize must be done after types are inferred"),
        )?;
        Ok(FunDecl {
            inferred_parameters: Some(closed_params),
            inferred_return_type: Some(closed_return_type),
            ..fun_decl
        })
    }

    fn finalize_decl(&mut self, decl: Decl) -> Result<Decl, TypeInferenceError> {
        let node = match decl.node {
            DeclKind::FunDecl(fun_decl) => DeclKind::FunDecl(self.finalize_fun(fun_decl)?),
            DeclKind::StructDecl {
                methods,
                name,
                generics,
                fields,
            } => {
                debug!("Finalizing struct {}", name);
                let methods = methods
                    .into_iter()
                    .map(|method| self.finalize_fun(method))
                    .collect::<Result<_, _>>()?;
                DeclKind::StructDecl {
                    methods,
                    name,
                    generics,
                    fields,
                }
            }
            DeclKind::EnumDecl {
                name,
                variants,
                generics,
                methods,
            } => {
                debug!("Finalizing enum {}", name);
                let methods: Vec<_> = methods
                    .into_iter()
                    .map(|method| self.finalize_fun(method))
                    .collect::<Result<_, _>>()?;
                DeclKind::EnumDecl {
                    name,
                    variants,
                    generics,
                    methods,
                }
            }
            _ => decl.node,
        };
        Ok(Decl { node, ..decl })
    }

    fn finalize_stmt(&mut self, stmt: Stmt) -> Result<Stmt, TypeInferenceError> {
        let node = match stmt.node {
            StmtKind::VarDecl(VarDecl {
                name,
                ty,
                value,
                inferred_ty,
            }) => {
                let finalized_ty = if let Some(ty) = inferred_ty {
                    self.close_type(&ty.into_rc())?
                } else {
                    return Err(TypeInferenceError::new(
                        ErrorKind::UnificationError,
                        stmt.location,
                        format!(
                            "Type inference failed, did not find type variable for {}",
                            name
                        ),
                    ));
                };
                StmtKind::VarDecl(VarDecl {
                    name,
                    ty,
                    value,
                    inferred_ty: Some((*finalized_ty).clone()),
                })
            }
            _ => stmt.node,
        };
        Ok(Stmt { node, ..stmt })
    }

    fn finalize_expr(&mut self, expr: Expr) -> Result<Expr, TypeInferenceError> {
        let node = match expr.node {
            ExprKind::Lambda(fun) => {
                let finalized_fun = self.finalize_fun(fun)?;
                Ok(ExprKind::Lambda(finalized_fun).into())
            }
            _ => Ok(expr.node),
        }?;

        let inferred_ty = if let Some(ty) = expr.inferred_ty {
            Some(self.close_type(&ty)?)
        } else {
            return Err(TypeInferenceError::new(
                ErrorKind::UnificationError,
                expr.location,
                "Type inference failed, did not find type variable".to_string(),
            ));
        };
        Ok(Expr {
            node,
            inferred_ty,
            ..expr
        })
    }
}

impl FunDecl {
    fn to_typescheme(&self, location: Location) -> Result<TypeScheme, TypeInferenceError> {
        let mut typed_params = vec![];
        for param in &self.parameters {
            let ty = param
                .ty
                .clone()
                .ok_or(TypeInferenceError::new(
                    ErrorKind::TypeExpected,
                    location,
                    "Function parameter".to_string(),
                ))?
                .into_type()
                .into_rc();
            typed_params.push(ty.clone());
        }

        let ret_ty_stated = self
            .return_type
            .clone()
            .ok_or(TypeInferenceError::new(
                ErrorKind::TypeExpected,
                location,
                "Function return type".to_string(),
            ))?
            .into_type()
            .into_rc();

        let ty = Type::create_function(typed_params.clone(), ret_ty_stated.clone());

        Ok(TypeScheme::create_function(
            self.generics.to_vec(),
            ty.into_rc(),
        ))
    }
}

/// Fills the methods with the struct and enum nodes from the Impl blocks.
/// Those blocks are not returned (they are effectively filtered out).
fn fill_methods(module: Module) -> Result<Module, TypeInferenceError> {
    // First, collect all the impls
    let mut impls = HashMap::<_, Vec<FunDecl>>::new();
    let mut rest = vec![];
    for decl in module.decls {
        match decl.node {
            DeclKind::ImplDecl {
                target, methods, ..
            } => {
                let exists = impls.insert(target.clone(), methods);
                if exists.is_some() {
                    return Err(TypeInferenceError::new(
                        ErrorKind::TypeMismatch,
                        decl.location,
                        format!("Multiple impl blocks for struct {}", target),
                    ));
                }
            }
            _ => rest.push(decl),
        }
    }

    let transformed = rest
        .into_iter()
        .map(|decl| match decl.node {
            DeclKind::StructDecl {
                name,
                generics,
                fields,
                ..
            } => {
                let methods = impls.remove(&name).unwrap_or(vec![]);
                Ok(Decl {
                    node: DeclKind::StructDecl {
                        methods,
                        name,
                        generics,
                        fields,
                    },
                    ..decl
                })
            }
            DeclKind::EnumDecl {
                name,
                variants,
                generics,
                ..
            } => {
                let methods = impls.remove(&name).unwrap_or(vec![]);
                Ok(Decl {
                    node: DeclKind::EnumDecl {
                        name,
                        variants,
                        generics,
                        methods,
                    },
                    ..decl
                })
            }
            _ => Ok(decl),
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(Module {
        decls: transformed,
        imports: module.imports,
    })
}

/// Traverse over module and collect all top types and identifiers.
fn precollect_types(module: &Module) -> Result<ModuleMetadata, TypeInferenceError> {
    let mut module_metadata = ModuleMetadata {
        types: HashMap::new(),
        ids: HashMap::new(),
    };
    // Collect all the types
    for decl in &module.decls {
        match &decl.node {
            DeclKind::StructDecl {
                name,
                fields,
                generics,
                methods,
            } => {
                let fields: HashMap<_, _> = fields
                    .iter()
                    .map(|StronglyTypedIdentifier { name, ty }| {
                        (name.clone(), ty.clone().into_type())
                    })
                    .collect();

                let methods = methods
                    .iter()
                    // TODO: This location is pointing at the struct, because we essentially
                    // lose the location of impl blocks. We should store the location of the
                    // impl block in the AST.
                    .map(|method| Ok((method.name.clone(), method.to_typescheme(decl.location)?)))
                    .collect::<Result<HashMap<_, _>, _>>()?;

                module_metadata.types.insert(
                    name.clone(),
                    TypeMetadata::Struct(StructMetadata {
                        generics: generics.iter().map(|g| g.name.clone()).collect(),
                        fields,
                        methods,
                    }),
                );
            }
            DeclKind::ImplDecl { .. } => {
                unreachable!("Impl blocks should be removed by now");
            }
            DeclKind::FunDecl(fun) => {
                let name = fun.name.clone();

                let fun_typescheme = fun.to_typescheme(decl.location)?;

                debug!("Adding function {} with type {}", name, fun_typescheme.ty);
                module_metadata.ids.insert(name.clone(), fun_typescheme);
            }
            DeclKind::EnumDecl {
                name,
                variants,
                generics,
                methods,
            } => {
                // The return type of the variant constructors. This needn't be a type scheme
                // since the functions will be type schemes.
                let enum_ty = Type::Constructor(Constructor {
                    name: name.clone(),
                    type_vec: generics
                        .iter()
                        .map(|g| Type::create_constant(g.name.clone()))
                        .collect(),
                })
                .into_rc();

                // Add the variants as function types
                for variant in variants {
                    let fields: Vec<Rc<Type>> = variant
                        .fields
                        .clone()
                        .into_iter()
                        .map(|field| field.into_type().into_rc())
                        .collect();
                    let fun_ty = TypeScheme {
                        ty: Type::create_function(fields.clone(), enum_ty.clone()).into_rc(),
                        generics: generics.clone(),
                    };
                    module_metadata.ids.insert(variant.name.clone(), fun_ty);
                }

                // In case the user imports the enum, we need to know what functions to export.
                module_metadata.types.insert(
                    name.clone(),
                    TypeMetadata::Enum {
                        variant_names: variants.iter().map(|v| v.name.clone()).collect(),
                        methods: methods
                            .iter()
                            // TODO: Again, bad location
                            .map(|method| {
                                Ok((method.name.clone(), method.to_typescheme(decl.location)?))
                            })
                            .collect::<Result<HashMap<_, _>, _>>()?,
                        generics: generics.iter().map(|g| g.name.clone()).collect(),
                    },
                );
            }
            DeclKind::TraitDecl { .. } => (),
        }
    }
    Ok(module_metadata)
}

/// Performs type inference.
/// Returns the same decls with the inferred types filled.
pub fn type_infer_modules(
    modules: HashMap<String, Module>,
) -> Result<HashMap<String, Module>, LastLayerError> {
    // Move methods from 'Impl' blocks into the structures
    let modules = modules
        .into_iter()
        .map(|(name, module)| {
            Ok((
                name.clone(),
                fill_methods(module).map_err(|e| LastLayerError {
                    location: e.location,
                    error: e.error,
                    module: name.clone(),
                })?,
            ))
        })
        .collect::<Result<HashMap<_, _>, _>>()?;

    // First, we need to collect all the types from all the modules.
    let mut module_metadata = modules
        .iter()
        .map(|(name, module)| {
            Ok((
                name.clone(),
                precollect_types(module).map_err(|e| LastLayerError {
                    location: e.location,
                    error: e.error,
                    module: name.clone(),
                })?,
            ))
        })
        .collect::<Result<HashMap<_, _>, _>>()?;

    // Also native functions
    let mut native_funs = ModuleMetadata {
        types: HashMap::new(),
        ids: HashMap::new(),
    };
    for native_fun in get_native_functions() {
        native_funs
            .ids
            .insert(native_fun.name.clone(), native_fun.ty.clone());
    }
    module_metadata.insert(STD_NATIVE_MODULE.to_string(), native_funs);

    // Perform type inference for each module
    let result: HashMap<String, Module> = modules
        .into_iter()
        .map(|(name, mut module)| {
            let metadata = module_metadata
                .get(&name)
                .expect("Internal compiler error, missing metadata");

            let symbol_table = RefCell::new(SymbolTable {
                unif_table: HashMap::new(),
                ids: IdEnv::new_with_init(metadata.ids.clone()),
                type_ids: metadata.types.clone(),
            });

            // Collect all the types from the imports
            for import in &module.imports {
                let imported_module_metadata = module_metadata
                    .get(&import.path)
                    .ok_or_else(|| {
                        TypeInferenceError::new(
                            ErrorKind::TypeMismatch,
                            import.location,
                            format!("Module {} not found in imports", import.path),
                        )
                    })
                    .map_err(|e| LastLayerError {
                        location: e.location,
                        error: e.error,
                        module: name.clone(),
                    })?;

                for named_import in &import.imported_ids {
                    symbol_table
                        .borrow_mut()
                        .collect_from_import(&[named_import], imported_module_metadata);
                }
            }

            // Do the actual type inference
            for decl in &mut module.decls {
                // TODO: Shouldn't we push a new scope here?
                symbol_table
                    .borrow_mut()
                    .visit_decl(decl)
                    .map_err(|o| LastLayerError {
                        location: o.location,
                        error: o.error,
                        module: name.clone(),
                    })?;
            }

            // Fold over (or rather for-each) over all the AST nodes and finalize the types (remove
            // type vars)
            let result = module
                .decls
                .into_iter()
                .map(|decl| {
                    decl.fold(
                        &|decl| symbol_table.borrow_mut().finalize_decl(decl),
                        &|stmt| symbol_table.borrow_mut().finalize_stmt(stmt),
                        &|expr| symbol_table.borrow_mut().finalize_expr(expr),
                    )
                })
                .collect::<Result<Vec<Decl>, _>>()
                .map_err(|e| LastLayerError {
                    location: e.location,
                    error: e.error,
                    module: name.clone(),
                })?;
            Ok((
                name,
                Module {
                    decls: result,
                    imports: module.imports,
                },
            ))
        })
        .collect::<Result<HashMap<String, Module>, _>>()?;

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::Import, frontend::parser::parse_ast};
    use regex::Regex;

    fn init() {
        // to enable envlogger in tests
        let _ = env_logger::builder().is_test(true).try_init();
    }

    #[test]
    fn test_filling_typescheme() {
        let type_scheme = TypeScheme::create_function(
            vec![GenericDeclaration {
                name: "T".to_string(),
            }],
            Type::create_function(
                vec![Type::Constructor(Constructor {
                    name: "Int".to_string(),
                    type_vec: vec![],
                })
                .into_rc()],
                Type::Constructor(Constructor {
                    name: "T".to_string(),
                    type_vec: vec![],
                })
                .into_rc(),
            )
            .into_rc(),
        );
        let filled = type_scheme
            .instantiate()
            .expect("Failed to instantiate typescheme");
        let pattern = r"^Function\[\?T\d+, Int\]$";
        let regex = Regex::new(pattern).unwrap();
        assert!(regex.is_match(&filled.to_string()));
    }

    fn infer_module(code: &str) -> Result<Vec<Decl>, LastLayerError> {
        let decls = parse_ast(code).unwrap().1;
        let mut modules = HashMap::new();
        modules.insert(
            "/main".to_string(),
            Module {
                decls,
                imports: vec![],
            },
        );
        let decls = type_infer_modules(modules)?;
        Ok(decls.get("/main").unwrap().decls.clone())
    }

    #[test]
    fn test_basic_inference() {
        let decls = infer_module("fn foo(x: Int): Int = { let y = x; let z = foo(y); foo(z) }");
        let result = "fn foo(x: Int): Int = { let y: Int = x; let z: Int = foo(y); foo(z) }";
        assert_eq!(decls.unwrap().first().unwrap().to_string(), result);
    }

    // Long time ago this worked (and it still could!), but since modules were implemented all
    // functions must be typed.
    // #[test]
    // fn test_basic_fun_inference() {
    //     let decls = infer_module("fn foo(x: Int) = 1");
    //     let result = "fn foo(x: Int): Int = 1";
    //     assert_eq!(decls.first().unwrap().to_string(), result);
    //
    //     let decls = infer_module("fn foo(x) = 1   fn bar(): Int = foo(1)");
    //     let result = "fn foo(x: Int): Int = 1   fn bar(): Int = foo(1)";
    //     assert_eq!(
    //         decls
    //             .iter()
    //             .map(|x| x.to_string())
    //             .collect::<Vec<_>>()
    //             .join("   "),
    //         result
    //     );
    // }

    #[test]
    fn test_enums_inference() {
        init();
        let decls = infer_module(
            "
enum Option[T] {
    Some(T),
    None,
}

enum List[T] {
    Cons(T, List[T]),
    Nil,
}

fn append[T](list: List[T], elem: T): List[T] = match list {
    Nil() => Cons(elem, Nil()),
    Cons(head, tail) => Cons(head, append(tail, elem)),
}

fn front[T](list: List[T]): Option[T] = match list {
    Cons(head, _) => Some(head),
    Nil() => None(),
}


fn main(): Int = {
    let lst = Nil();
    let appended = Cons(1, lst);
    match front(appended) {
        Some(x) => x,
        None() => 0,
    }
}
",
        )
        .unwrap();
        assert!(decls.len() == 5);
        assert!(decls[4].to_string().contains("fn main(): Int = {"));
        assert!(decls[4].to_string().contains("let lst: List[Int] = Nil();"));
        assert!(decls[4]
            .to_string()
            .contains("let appended: List[Int] = Cons(1, lst);"));
    }

    #[test]
    fn test_match_with_cond() {
        init();
        let decls = infer_module(
            "
enum Option[T] {
    Some(T),
    None,
}

enum List[T] {
    Cons(T, List[T]),
    Nil,
}

fn find[T](lst: List[T], n: T): Bool = match lst {
    Cons(head, tail) if head == n => true,
    Cons(head, tail) => find(tail, n),
    Nil => false,
}

fn main(): Int = {
    let lst = Cons(0, Cons(1, Cons(2, Cons(3, Nil()))));
    let exists = find(lst, 2);
    0
}
",
        )
        .unwrap();
        assert!(decls.len() == 4);
        assert!(decls[3].to_string().contains("let lst: List[Int]"));
        assert!(decls[3].to_string().contains("let exists: Bool"));

        let decls = infer_module(
            "
fn main(): Int = {
    match 1 {
        1 if 0 => 1,
        _ => 0,
    }
}
",
        );
        assert!(decls.is_err());
    }

    #[test]
    fn test_structs_inference() {
        init();
        let decls = infer_module(
            "
struct Point {
    x: Int,
    y: Int,
}

fn main(): Int = {
    let p = &Point { x: 1, y: 2 };
    let x = p.x;
    let y = p.y;
    p.x + p.y
}
",
        )
        .unwrap();

        assert!(decls[1].to_string().contains("fn main(): Int = {"));
        assert!(decls[1]
            .to_string()
            .contains("let p: Point = Point { x: 1, y: 2 };"));
        assert!(decls[1].to_string().contains("let x: Int = p.x;"));
        assert!(decls[1].to_string().contains("let y: Int = p.y;"));

        let decls = infer_module(
            "
struct Point {
    x: Int,
    y: Int,
}

fn main(): Int = {
    let p = &Point { x: 1, y: 2 };
    let sum = p.x + p.z;
    sum
}
",
        );
        assert!(decls.is_err());

        let decls = infer_module(
            "
struct Point {
    x: Int,
    y: Int,
}

fn main(): Int = {
    let p = &Point { x: 1, z: 2 };
    let sum = p.x + p.z;
    sum
}
",
        );
        assert!(decls.is_err());
    }

    #[test]
    fn test_structs_with_generics() {
        init();
        let decls = infer_module(
            "
struct Point[T] {
    x: T,
    y: T,
}

fn main(): Int = {
    let p = &Point[Int] { x: 1, y: 2 };
    let sum = p.x + p.y;
    sum
}
",
        )
        .unwrap();

        assert!(decls[1].to_string().contains("fn main(): Int = {"));
        assert!(decls[1]
            .to_string()
            .contains("let p: Point[Int] = Point[Int] { x: 1, y: 2 };"));
        assert!(decls[1].to_string().contains("let sum: Int"));
    }

    #[test]
    fn test_struct_match() {
        init();
        let decls = infer_module(
            "
struct Point {
    x: Int,
    y: Int,
}

fn main(): Int = {
    let p = &Point { x: 1, y: 2 };
    let sum = match p {
        Point { x, y } => x + y,
    };
    sum
}
",
        )
        .unwrap();

        assert!(decls[1].to_string().contains("fn main(): Int = {"));
        assert!(decls[1]
            .to_string()
            .contains("let p: Point = Point { x: 1, y: 2 };"));
        assert!(decls[1].to_string().contains("let sum: Int"));
    }

    #[test]
    fn test_imports() {
        init();
        // The import syntax works with filesystem.
        // Instead, in here, we will hardcode the imports to the
        // structure.
        let main = parse_ast(
            "
fn main(): Int = {
    let p = foo();
    bar(p)
}
",
        )
        .unwrap();
        let import = parse_ast(
            "
fn foo(): Int = 1
fn bar(x: Int): Int = x * 2
            ",
        )
        .unwrap();

        let mut modules = HashMap::new();
        modules.insert(
            "/main".to_string(),
            Module {
                decls: main.1,
                imports: vec![Import {
                    path: "/foobar".to_string(),
                    imported_ids: vec!["foo".to_string(), "bar".to_string()],
                    location: Location::new(0, 0),
                }],
            },
        );

        modules.insert(
            "/foobar".to_string(),
            Module {
                decls: import.1,
                imports: vec![],
            },
        );

        let decls = type_infer_modules(modules).unwrap();
        let main = decls.get("/main").unwrap();
        assert!(main.decls[0].to_string().contains("let p: Int = foo();"));
    }

    #[test]
    fn test_imports_complicated() {
        init();
        let f1 = parse_ast(
            "
fn main(): Int = {
    let p = foo();
    bar(p)
}
",
        )
        .unwrap();
        let f2 = parse_ast(
            "
fn foo(): Int = 1
fn bar(x: Int): Int = double_value(x)
            ",
        )
        .unwrap();
        let f3 = parse_ast(
            "
fn double_value(x: Int): Int = x * 2
            ",
        )
        .unwrap();

        let mut modules = HashMap::new();
        modules.insert(
            "/f1".to_string(),
            Module {
                decls: f1.1,
                imports: vec![Import {
                    path: "/f2".to_string(),
                    imported_ids: vec!["foo".to_string(), "bar".to_string()],
                    location: Location::new(0, 0),
                }],
            },
        );

        modules.insert(
            "/f2".to_string(),
            Module {
                decls: f2.1,
                imports: vec![Import {
                    path: "/f3".to_string(),
                    imported_ids: vec!["double_value".to_string()],
                    location: Location::new(0, 0),
                }],
            },
        );

        modules.insert(
            "/f3".to_string(),
            Module {
                decls: f3.1,
                imports: vec![],
            },
        );

        let decls = type_infer_modules(modules).unwrap();
        let main = decls.get("/f1").unwrap();
        assert!(main.decls[0].to_string().contains("let p: Int = foo();"));
    }

    #[test]
    fn test_import_non_existing_identifier() {
        init();
        let main = parse_ast(
            "
            fn main(): Int = {
                let x = non_existing_function();
                0
            }
            ",
        )
        .unwrap();

        let mut modules = HashMap::new();
        modules.insert(
            "/main".to_string(),
            Module {
                decls: main.1,
                imports: vec![Import {
                    path: STD_NATIVE_MODULE.to_string(),
                    imported_ids: vec!["non_existing_function".to_string()],
                    location: Location::new(0, 0),
                }],
            },
        );

        let result = type_infer_modules(modules);
        assert!(result.is_err());
    }

    #[test]
    fn test_import_non_existing_module() {
        init();
        let main = parse_ast(
            "
            fn main(): Int = {
                let x = non_existing_function();
                0
            }
            ",
        )
        .unwrap();

        let mut modules = HashMap::new();
        modules.insert(
            "/main".to_string(),
            Module {
                decls: main.1,
                imports: vec![Import {
                    path: "/non_existing_module".to_string(),
                    imported_ids: vec!["non_existing_function".to_string()],
                    location: Location::new(0, 0),
                }],
            },
        );

        let result = type_infer_modules(modules);
        assert!(result.is_err());
    }

    #[test]
    fn test_import_function_with_incorrect_argument_types() {
        init();
        let main = parse_ast(
            "
            fn main(): Int = {
                let x = imported_function(1, true);
                0
            }
            ",
        )
        .unwrap();

        let imported_module = parse_ast(
            "
            fn imported_function(a: Int, b: Int): Int = a + b
            ",
        )
        .unwrap();

        let mut modules = HashMap::new();
        modules.insert(
            "/main".to_string(),
            Module {
                decls: main.1,
                imports: vec![Import {
                    path: "/imported_module".to_string(),
                    imported_ids: vec!["imported_function".to_string()],
                    location: Location::new(0, 0),
                }],
            },
        );

        modules.insert(
            "/imported_module".to_string(),
            Module {
                decls: imported_module.1,
                imports: vec![],
            },
        );

        let result = type_infer_modules(modules);
        assert!(result.is_err());
    }

    #[test]
    fn test_native_function() {
        init();
        let main = parse_ast(
            "
fn main(): Int = {
    let x = pow(2, 3);
    assert(true);
    0
}
",
        )
        .unwrap();

        let mut modules = HashMap::new();
        modules.insert(
            "/main".to_string(),
            Module {
                decls: main.1,
                imports: vec![Import {
                    path: STD_NATIVE_MODULE.to_string(),
                    imported_ids: vec!["pow".to_string(), "assert".to_string()],
                    location: Location::new(0, 0),
                }],
            },
        );

        let decls = type_infer_modules(modules)
            .unwrap()
            .get("/main")
            .unwrap()
            .decls
            .clone();

        assert!(decls.len() == 1);
        assert!(decls[0].to_string().contains("let x: Int"));
    }

    #[test]
    fn test_methods() {
        init();
        let decls = infer_module(
            "
enum Option[T] {
    Some(T),
    None,
}

impl Option[T] {
    fn is_some(): Bool = match self {
        Some(_) => true,
        None => false,
    }

    fn is_none(): Bool = {
        let self_alias = self;
        self_alias.is_some() == false
    }

    fn map[U](f: (T) => U): Option[U] = match self {
        Some(x) => Some(f(x)),
        None => None(),
    }
}

fn is_odd(x: Int): Bool = x % 2 == 1

fn main(): Int = {
    let x = Some(1);
    let y = x.is_some();
    let z = x.is_none();
    let odd = x.map(is_odd);
    0
}
",
        )
        .unwrap();

        assert_eq!(decls.len(), 3);
        if let DeclKind::EnumDecl {
            name,
            variants,
            generics,
            methods,
        } = &decls[0].node
        {
            assert_eq!(name, "Option");
            assert_eq!(variants.len(), 2);
            assert_eq!(generics.len(), 1);
            assert_eq!(methods.len(), 3);

            let is_none = methods.iter().find(|m| m.name == "is_none").unwrap();
            assert!(is_none
                .body
                .to_string()
                .contains("let self_alias: Option[T] = self;"));
        } else {
            panic!("Expected EnumDecl")
        }
        assert!(decls[2]
            .to_string()
            .contains("let x: Option[Int] = Some(1);"));
        assert!(decls[2].to_string().contains("let y: Bool = x.is_some();"));
        assert!(decls[2].to_string().contains("let z: Bool = x.is_none();"));
        assert!(decls[2]
            .to_string()
            .contains("let odd: Option[Bool] = x.map(is_odd);"));
    }

    #[test]
    fn test_lambda() {
        init();
        let decls = infer_module(
            "
fn main(): Int = {
    let f = |x| { x + 1 };
    f(1)
}
",
        )
        .unwrap();

        assert_eq!(decls.len(), 1);
        assert!(decls[0]
            .to_string()
            .contains("let f: Function[Int, Int] = fn AnonymousFunction(x: Int): Int ="));

        let decls = infer_module(
            "
fn main(): Int = {
    let f = |x, y| { x + y };
    f(1, 2)
}
",
        )
        .unwrap();

        assert_eq!(decls.len(), 1);
        assert!(decls[0].to_string().contains(
            "let f: Function[Int, Int, Int] = fn AnonymousFunction(x: Int, y: Int): Int ="
        ));
    }
}
