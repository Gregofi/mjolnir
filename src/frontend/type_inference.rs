/// TODO: Check if the Rcs are truly necessary.
use super::utils::{GenericDeclaration, IdEnv, StronglyTypedIdentifier, WrittenType};
use crate::ast::{Decl, DeclKind, Expr, ExprKind, Operator, Pattern, Stmt, StmtKind, VarDecl};
use log::debug;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum TypeInferenceError {
    TypeMismatch(String),
    UnificationError(String),
}

impl Display for TypeInferenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeInferenceError::TypeMismatch(s) => write!(f, "Type mismatch: {}", s),
            TypeInferenceError::UnificationError(s) => write!(f, "Unification error: {}", s),
        }
    }
}

/// Generate new typevar
fn new_typevar() -> Type {
    static mut COUNTER: usize = 0;
    // TODO: Get rid of this unsafe piece of a guy
    Type::TypeVar(TypeVar(unsafe {
        COUNTER += 1;
        COUNTER
    }))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeVar(usize);

/// Constructors are the types that are defined in the source code. For example, Int, List<T>,
/// Either<L, R>, etc. Also functions are represented via constructors. Function<ReturnType,
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
    generics: Vec<GenericDeclaration>,
    ty: Rc<Type>,
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
    fn create_function(generics: Vec<GenericDeclaration>, ty: Rc<Type>) -> Self {
        Self { generics, ty }
    }

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
                Err(TypeInferenceError::UnificationError(
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
    fn into_rc(self) -> Rc<Type> {
        Rc::new(self)
    }

    fn create_constant(name: String) -> Rc<Type> {
        Type::Constructor(Constructor {
            name,
            type_vec: vec![],
        })
        .into_rc()
    }

    /// Converts this type into TypeScheme without any generics
    fn into_scheme(self) -> TypeScheme {
        TypeScheme {
            generics: vec![],
            ty: self.into_rc(),
        }
    }

    /// Function is represented as a constructor Function<ReturnType, ...Args>
    fn create_function(mut parameters: Vec<Rc<Type>>, return_type: Rc<Type>) -> Type {
        parameters.insert(0, return_type);
        Type::Constructor(Constructor {
            name: "Function".to_string(),
            type_vec: parameters,
        })
    }

    /// Creates a new type where every occurence of each variable in map is replaced.
    /// If the type is a constructor which name matches the name in map,
    /// the replacement cannot be performed and error will be returned.
    /// (T<Q>, { T -> CustomType }) => CustomType<Q> will result in an error.
    fn fill_types(&self, map: &HashMap<String, Rc<Type>>) -> Result<Rc<Type>, TypeInferenceError> {
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
    fields: Vec<(String, Type)>,
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

#[derive(Debug, Clone)]
enum TypeMetadata {
    Struct(StructMetadata),
}

pub struct SymbolTable {
    /// A table of type variables and their corresponding types.
    unif_table: HashMap<TypeVar, Rc<Type>>,
    ids: IdEnv<TypeScheme>,
    type_ids: HashMap<String, TypeMetadata>,
}

impl SymbolTable {
    fn unify(&mut self, t1: &Rc<Type>, t2: &Rc<Type>) -> Result<(), TypeInferenceError> {
        debug!("Unifying ⟦{}⟧ = ⟦{}⟧", t1, t2);
        match (t1.as_ref(), t2.as_ref()) {
            (Type::TypeVar(tv), other) | (other, Type::TypeVar(tv)) => {
                let t = self.unif_table.get(tv);
                let other = if std::ptr::eq(other, t1.as_ref()) {
                    t1
                } else {
                    t2
                };
                if let Some(t) = t {
                    self.unify(&t.clone(), other)?;
                }

                self.unif_table.insert(tv.clone(), other.clone());
            }
            (Type::Constructor(c1), Type::Constructor(c2)) if c1.name == c2.name => {
                for (t1, t2) in c1.type_vec.iter().zip(c2.type_vec.iter()) {
                    self.unify(t1, t2)?;
                }
            }
            _ => {
                return Err(TypeInferenceError::UnificationError(format!(
                    "Unification error, cannot unify ⟦{}⟧ = ⟦{}⟧",
                    t1, t2
                )))
            }
        }
        Ok(())
    }

    fn visit_decl(&mut self, decl: &mut Decl) -> Result<(), TypeInferenceError> {
        match &mut decl.node {
            DeclKind::FunDecl {
                name,
                generics,
                parameters,
                return_type,
                body,
                inferred_parameters,
                inferred_return_type,
            } => {
                debug!("Visiting function {}", name);
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
                let fun_scheme =
                    TypeScheme::create_function(generics.to_vec(), fun_ty.clone().into_rc());

                debug!("Adding function {} with type {}", name, fun_ty);
                self.ids.insert(name.clone(), fun_scheme);

                // Visiting the function body must be done at the
                // end, when we have all the types in the symbol table.
                // Otherwise recursive functions will not work.
                let ret_ty = self.visit_expr(body)?;
                self.unify(&ret_ty_stated, &ret_ty)?;

                decl.inferred_ty = Some(fun_ty.clone());
            }
            DeclKind::EnumDecl {
                name,
                variants,
                generics,
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
                    self.ids.insert(variant.name.clone(), fun_ty);
                }
            }
            DeclKind::StructDecl { .. } => {
                // noop, collecting happens before actual type inference
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
                self.unify(&var_ty, &value_ty)?;
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
            ExprKind::Identifier(id) => {
                let ty = match self.ids.get(id) {
                    Some(ty) => ty.instantiate()?,
                    None => Err(TypeInferenceError::TypeMismatch(format!(
                        "Type variable not found for {}",
                        id
                    )))?,
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

                self.unify(&target_type, &fun_ty)?;

                Ok(ret_ty)
            }
            ExprKind::If { cond, then, els } => {
                let cond_ty = self.visit_expr(cond)?;
                let then_ty = self.visit_expr(then)?;
                let else_ty = self.visit_expr(els)?;

                self.unify(&cond_ty, &Type::create_constant("Bool".to_string()))?;

                self.unify(&then_ty, &else_ty)?;

                Ok(then_ty)
            }
            ExprKind::Binary { op, lhs, rhs, .. } => {
                // TODO: The types must be the same and, if the operator is a
                // comparison operator, the result must be a bool.
                let lhs_ty = self.visit_expr(lhs)?;
                let rhs_ty = self.visit_expr(rhs)?;
                self.unify(&lhs_ty, &rhs_ty)?;

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

                    self.unify_pattern(&arm.pattern, &target_ty)?;

                    if let Some(arm_cond) = arm.cond.as_mut() {
                        let ty = self.visit_expr(arm_cond)?;
                        debug!("Unifying condition with type {}", ty);
                        self.unify(&ty, &Type::create_constant("Bool".to_string()))?;
                    }

                    let arm_ty = self.visit_expr(&mut arm.body)?;
                    self.unify(&ret_ty, &arm_ty)?;
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
                // StructFoo<T> { x: T};
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
                        return Err(TypeInferenceError::TypeMismatch(format!(
                            "Struct {} not found; name used as struct initializer",
                            name
                        )))
                    }
                };

                let fields_typed = struct_metadata.instantiate_struct(&struct_type)?;

                // Check that the field initializers have correct types.
                for (field_name, field_expr) in fields {
                    let field_ty = match fields_typed.get(field_name) {
                        Some(ty) => ty,
                        None => {
                            return Err(TypeInferenceError::TypeMismatch(format!(
                                "Field {} not found in struct {}",
                                field_name, name
                            )))
                        }
                    };

                    let expr_ty = self.visit_expr(field_expr)?;
                    self.unify(&expr_ty, field_ty)?;
                }

                Ok(Type::Constructor(struct_type).into_rc())
            }
            ExprKind::MemberAccess { target, member } => {
                let ty = self.visit_expr(target)?;

                let closed_ty = self.close_type(&ty)?;
                let cons = match closed_ty.as_ref() {
                    Type::Constructor(cons) => cons,
                    _ => {
                        return Err(TypeInferenceError::TypeMismatch(
                            "The type of the struct must be known at this point".to_string(),
                        ))
                    }
                };

                let struct_metadata = match self.type_ids.get(&cons.name) {
                    Some(TypeMetadata::Struct(metadata)) => metadata,
                    _ => {
                        return Err(TypeInferenceError::TypeMismatch(format!(
                            "Struct {} not found when accessing member {}",
                            cons.name, member
                        )))
                    }
                };

                let member = match struct_metadata
                    .fields
                    .iter()
                    .find(|(name, _)| name == member)
                {
                    Some((_, ty)) => ty.clone().into_rc(),
                    None => {
                        return Err(TypeInferenceError::TypeMismatch(format!(
                            "Field {} not found in struct {}",
                            member, cons.name
                        )))
                    }
                };

                let types = struct_metadata
                    .generics
                    .iter()
                    .zip(cons.type_vec.iter())
                    .fold(HashMap::new(), |mut map, (g, t)| {
                        map.insert(g.clone(), t.clone());
                        map
                    });

                member.fill_types(&types)
            }
        }?;
        expr.inferred_ty = Some(res.clone());
        Ok(res)
    }

    fn unify_pattern(
        &mut self,
        pattern: &Pattern,
        target_ty: &Rc<Type>,
    ) -> Result<(), TypeInferenceError> {
        match (pattern, target_ty.as_ref()) {
            (Pattern::Wildcard, _) => Ok(()),
            (Pattern::Int(_), _) => {
                self.unify(target_ty, &Type::create_constant("Int".to_string()))
            }
            (Pattern::Boolean(_), _) => {
                self.unify(target_ty, &Type::create_constant("Bool".to_string()))
            }
            (Pattern::String(_), _) => {
                self.unify(target_ty, &Type::create_constant("String".to_string()))
            }
            (Pattern::Struct { name, fields }, _) => {
                let struct_metadata = match self.type_ids.get(name) {
                    Some(TypeMetadata::Struct(metadata)) => metadata,
                    _ => {
                        return Err(TypeInferenceError::TypeMismatch(format!(
                            "Struct {} not found when matching patterns",
                            name
                        )))
                    }
                };

                let closed_target = self.close_type(target_ty)?;
                let c = match closed_target.as_ref() {
                    Type::Constructor(c) => c,
                    _ => {
                        return Err(TypeInferenceError::TypeMismatch(format!(
                            "Type must be known at this point: {}",
                            target_ty
                        )))
                    }
                };

                if c.name != *name {
                    return Err(TypeInferenceError::TypeMismatch(format!(
                        "Expected struct {}, got {}",
                        name, c.name
                    )));
                }

                let struct_type = struct_metadata.instantiate_struct(c)?;

                for field in fields.iter() {
                    let field_ty = match struct_type.get(field) {
                        Some(ty) => ty.as_ref().clone(),
                        None => {
                            return Err(TypeInferenceError::TypeMismatch(format!(
                                "Field {} not found in struct {}",
                                field, name
                            )))
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
                    Some(cons) => Ok(cons),
                    None => Err(TypeInferenceError::TypeMismatch(format!(
                        "Enum constructor not found for {}",
                        name
                    ))),
                }?;

                // The order of generics correspond to the order of the types in the return
                // constructor.
                // TODO: The type must be at least partially known at this point.
                // Consider if this requirement is necessary.
                let finalized_target = self.close_type(target_ty)?;
                let instantiated_generics = match finalized_target.as_ref() {
                    Type::Constructor(Constructor { type_vec, .. }) => type_vec,
                    _ => {
                        return Err(TypeInferenceError::TypeMismatch(format!(
                            "Type must be known at this point: {}",
                            target_ty
                        )));
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

                // Now we have the type of the constructor, we can check the types of the patterns
                let cons = match cons_inst.as_ref() {
                    Type::Constructor(cons) => cons,
                    _ => {
                        return Err(TypeInferenceError::TypeMismatch(format!(
                            "Expected constructor, got {}",
                            cons_inst
                        )))
                    }
                };

                let params = cons.type_vec[1..].iter();
                for (pattern, ty) in patterns.iter().zip(params) {
                    self.unify_pattern(pattern, ty)?;
                }
                Ok(())
            }
            (Pattern::Identifier(name), ty) => {
                self.ids.insert(name.clone(), (*ty).clone().into_scheme());
                Ok(())
            }
        }
    }

    fn close_type(&self, ty: &Rc<Type>) -> Result<Rc<Type>, TypeInferenceError> {
        match ty.as_ref() {
            Type::TypeVar(TypeVar(id)) => {
                let t = self.unif_table.get(&TypeVar(*id)).ok_or_else(|| {
                    TypeInferenceError::UnificationError(format!(
                        "Did not find Type variable ?T{} in unification table",
                        id
                    ))
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

    fn finalize_decl(&mut self, decl: Decl) -> Result<Decl, TypeInferenceError> {
        let node = match decl.node {
            DeclKind::FunDecl {
                name,
                generics,
                parameters,
                inferred_parameters,
                return_type,
                inferred_return_type,
                body,
            } => {
                let closed_params = inferred_parameters
                    .expect("Finalize must be done after types are inferred")
                    .into_iter()
                    .map(|t| self.close_type(&t))
                    .collect::<Result<Vec<_>, _>>()?;

                let closed_return_type = self.close_type(
                    &inferred_return_type.expect("Finalize must be done after types are inferred"),
                )?;
                DeclKind::FunDecl {
                    name,
                    generics,
                    parameters,
                    inferred_parameters: Some(closed_params),
                    return_type,
                    inferred_return_type: Some(closed_return_type),
                    body,
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
                    return Err(TypeInferenceError::UnificationError(format!(
                        "Type inference failed, did not find type variable for {}",
                        name
                    )));
                };
                println!("Inferred type of {} is {}", name, finalized_ty);
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
}

pub fn type_inference(mut decls: Vec<Decl>) -> Result<Vec<Decl>, TypeInferenceError> {
    // Previsit decls, collect necessary info about types.
    let mut type_ids = HashMap::new();
    for decl in &decls {
        if let DeclKind::StructDecl { name, fields, generics } = &decl.node {
            let fields: Vec<_> = fields
                .iter()
                .map(|StronglyTypedIdentifier { name, ty }| {
                    (name.clone(), ty.clone().into_type())
                })
                .collect();

            type_ids.insert(
                name.clone(),
                TypeMetadata::Struct(StructMetadata {
                    generics: generics.iter().map(|g| g.name.clone()).collect(),
                    fields,
                }),
            );
        }
    }

    // Wrap it in refcell so we can use it in the closures.
    let symbol_table = RefCell::new({
        let mut table = SymbolTable {
            unif_table: HashMap::new(),
            ids: IdEnv::new(),
            type_ids,
        };
        table.ids.push();
        table
    });

    // Do the actual type inference
    for decl in decls.iter_mut() {
        symbol_table.borrow_mut().visit_decl(decl)?;
    }

    // Close all the types (eliminate type variables)
    decls
        .into_iter()
        .map(|decl| {
            decl.fold(
                &|decl| symbol_table.borrow_mut().finalize_decl(decl),
                &|stmt| symbol_table.borrow_mut().finalize_stmt(stmt),
                &|mut expr| {
                    expr.inferred_ty = if let Some(ty) = expr.inferred_ty {
                        Some(symbol_table.borrow_mut().close_type(&ty)?)
                    } else {
                        return Err(TypeInferenceError::UnificationError(
                            "Type inference failed, did not find type variable".to_string(),
                        ));
                    };
                    Ok(expr)
                },
            )
        })
        .collect::<Result<_, _>>()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::parser::parse_ast;
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

    #[test]
    fn test_basic_inference() {
        let ast = parse_ast("fn foo(x: Int): Int = { let y = x; let z = foo(y); foo(z) }");
        let decls = type_inference(ast.unwrap()).unwrap();
        let result = "fn foo(x: Int): Int = { let y: Int = x; let z: Int = foo(y); foo(z) }";
        assert_eq!(decls.first().unwrap().to_string(), result);
    }

    #[test]
    fn test_basic_fun_inference() {
        let ast = parse_ast("fn foo(x: Int) = 1");
        let decls = type_inference(ast.unwrap()).unwrap();
        let result = "fn foo(x: Int): Int = 1";
        assert_eq!(decls.first().unwrap().to_string(), result);

        let ast = parse_ast("fn foo(x) = 1   fn bar(): Int = foo(1)");
        let decls = type_inference(ast.unwrap()).unwrap();
        let result = "fn foo(x: Int): Int = 1   fn bar(): Int = foo(1)";
        assert_eq!(
            decls
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join("   "),
            result
        );
    }

    #[test]
    fn test_enums_inference() {
        init();
        let ast = parse_ast(
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
        );
        let decls = type_inference(ast.unwrap()).unwrap();
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
        let ast = parse_ast(
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
        );
        let decls = type_inference(ast.unwrap()).unwrap();

        assert!(decls.len() == 4);
        assert!(decls[3].to_string().contains("let lst: List[Int]"));
        assert!(decls[3].to_string().contains("let exists: Bool"));

        let ast = parse_ast(
            "
fn main(): Int = {
    match 1 {
        1 if 0 => 1,
        _ => 0,
    }
}
",
        );
        assert!(type_inference(ast.unwrap()).is_err());
    }

    #[test]
    fn test_structs_inference() {
        init();
        let ast = parse_ast(
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
        );

        let decls = type_inference(ast.unwrap()).unwrap();
        println!("{}\n", decls[1]);
        assert!(decls[1].to_string().contains("fn main(): Int = {"));
        assert!(decls[1]
            .to_string()
            .contains("let p: Point = Point { x: 1, y: 2 };"));
        assert!(decls[1].to_string().contains("let x: Int = p.x;"));
        assert!(decls[1].to_string().contains("let y: Int = p.y;"));

        let ast = parse_ast(
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

        let decls = type_inference(ast.unwrap());
        assert!(decls.is_err());

        let ast = parse_ast(
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

        let decls = type_inference(ast.unwrap());
        assert!(decls.is_err());
    }

    #[test]
    fn test_structs_with_generics() {
        init();
        let ast = parse_ast(
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
        );

        let decls = type_inference(ast.unwrap()).unwrap();
        println!("{}\n", decls[1]);
        assert!(decls[1].to_string().contains("fn main(): Int = {"));
        assert!(decls[1]
            .to_string()
            .contains("let p: Point[Int] = Point[Int] { x: 1, y: 2 };"));
        assert!(decls[1].to_string().contains("let sum: Int"));
    }

    #[test]
    fn test_struct_match() {
        init();
        let ast = parse_ast(
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
        );

        let decls = type_inference(ast.unwrap()).unwrap();
        println!("{}\n", decls[1]);
        assert!(decls[1].to_string().contains("fn main(): Int = {"));
        assert!(decls[1]
            .to_string()
            .contains("let p: Point = Point { x: 1, y: 2 };"));
        assert!(decls[1].to_string().contains("let sum: Int"));
    }
}
