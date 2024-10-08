/*
Takes the inferred type and a table from type identifiers
to TypeInfo and types the AST from the 'weakly' typed AST,
where types are represented as strings/constructors from
type inference into a fully typed AST.

This step is expected to be run after type inference.
*/

use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};
use std::rc::Rc;

use log::debug;

use crate::ast::*;
use crate::frontend::types::TypeInfo;
use crate::location::Location;

use super::error::{FrontEndError, LastLayerError};
use super::type_inference::{Constructor, Type as InferredType};
use super::types::InstantiatedType;
use super::utils::{StronglyTypedIdentifier, TypedIdentifier, WrittenType};

#[derive(Debug, Clone)]
pub enum TypeAstErrKind {
    NonExistingType,
    #[allow(dead_code)]
    Untyped,
}

type TypeAstErr = FrontEndError<TypeAstErrKind>;

impl WrittenType {
    fn to_instantiated_type(&self) -> Result<InstantiatedType, TypeAstErr> {
        match self {
            WrittenType::Identifier { name, generics } => {
                let generics = generics
                    .iter()
                    .map(|g| g.to_instantiated_type())
                    .collect::<Result<_, _>>()?;
                Ok(InstantiatedType {
                    ty: name.clone(),
                    generics,
                })
            }
            WrittenType::Function { .. } => todo!(),
        }
    }
}

impl InferredType {
    /// Esentially removes the type variables from the type information, type variables must not
    /// exist at the point of using this function. Ie. do this after type inference.
    fn to_instantiated_type(&self, location: Location) -> Result<InstantiatedType, TypeAstErr> {
        match self {
            InferredType::TypeVar(_) => Err(TypeAstErr::new(
                TypeAstErrKind::NonExistingType,
                location,
                "Compiler bug: Cannot have type variables when typing AST".to_string(),
            )),
            InferredType::Constructor(Constructor { name, type_vec }) => {
                let generics = type_vec
                    .iter()
                    .map(|arg| arg.to_instantiated_type(location))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(InstantiatedType {
                    ty: name.clone(),
                    generics,
                })
            }
        }
    }
}

impl FunDecl {
    fn type_ast(self) -> Result<TypedFunDecl, TypeAstErr> {
        debug!("Typing function declaration: {}", self.name);

        let parameters = self
            .inferred_parameters
            .expect("Compiler bug: Type inference must be done at this point")
            .into_iter()
            .zip(self.parameters)
            .map(|(ty, param)| {
                // TODO: Location
                let ty = ty.to_instantiated_type(Location::new(0, 0))?;
                Ok(TypedIdentifier {
                    name: param.name,
                    ty,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let return_type = self
            .inferred_return_type
            .expect("Compiler bug: Type inference must be done at this point")
            .to_instantiated_type(Location::new(0, 0))?;
        let body = self.body.type_ast(&HashMap::new())?;
        Ok(TypedFunDecl {
            name: self.name,
            parameters,
            return_type,
            body: Box::new(body),
        })
    }
}

impl Decl {
    pub fn type_ast(self) -> Result<TypedDecl, TypeAstErr> {
        let typed_kind = match self.node {
            DeclKind::FunDecl(fun_decl) => TypedDeclKind::FunDecl(fun_decl.type_ast()?),
            DeclKind::StructDecl {
                name,
                fields,
                methods,
                ..
            } => {
                let fields = fields
                    .into_iter()
                    .map(|StronglyTypedIdentifier { name, ty }| {
                        let ty = ty.to_instantiated_type()?;
                        Ok(TypedIdentifier { name, ty })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let methods = methods
                    .into_iter()
                    .map(|fun_decl| fun_decl.type_ast())
                    .collect::<Result<Vec<_>, _>>()?;
                TypedDeclKind::StructDecl {
                    name,
                    fields,
                    methods,
                }
            }
            DeclKind::EnumDecl {
                name,
                variants,
                methods,
                ..
            } => {
                let methods = methods
                    .into_iter()
                    .map(|fun_decl| fun_decl.type_ast())
                    .collect::<Result<Vec<_>, _>>()?;
                TypedDeclKind::EnumDecl {
                    name,
                    variants,
                    methods,
                }
            }
            DeclKind::TraitDecl { .. } => todo!(),
            DeclKind::ImplDecl { .. } => todo!(),
        };

        Ok(TypedDecl {
            node: typed_kind,
            location: self.location,
        })
    }
}

impl Stmt {
    pub fn type_ast(
        self,
        type_table: &HashMap<String, Rc<TypeInfo>>,
    ) -> Result<TypedStmt, TypeAstErr> {
        let node = match self.node {
            StmtKind::VarDecl(vardecl) => TypedStmtKind::VarDecl(TypedVarDecl {
                name: vardecl.name,
                value: Box::new(vardecl.value.type_ast(type_table)?),
            }),
            StmtKind::Expr(e) => TypedStmtKind::Expr(e.type_ast(type_table)?),
        };
        Ok(TypedStmt {
            node,
            location: self.location,
        })
    }
}

impl Expr {
    pub fn type_ast(
        self,
        type_table: &HashMap<String, Rc<TypeInfo>>,
    ) -> Result<TypedExpr, TypeAstErr> {
        let ty = if let Some(ty) = &self.inferred_ty {
            ty.to_instantiated_type(self.location)?
        } else {
            panic!("Compiler bug: Cannot type AST without inferred types");
        };

        let node = match self.node {
            ExprKind::Compound(stmts, e) => {
                let stmts = stmts
                    .into_iter()
                    .map(|stmt| stmt.type_ast(type_table))
                    .collect::<Result<Vec<_>, _>>()?;
                let e = e.type_ast(type_table)?;
                ExprKind::Compound(stmts, Box::new(e))
            }
            ExprKind::FunCall { target, args } => {
                let target = target.type_ast(type_table)?;
                let args = args
                    .into_iter()
                    .map(|arg| arg.type_ast(type_table))
                    .collect::<Result<Vec<_>, _>>()?;
                ExprKind::FunCall {
                    target: Box::new(target),
                    args,
                }
            }
            ExprKind::If { cond, then, els } => {
                let cond = Box::new(cond.type_ast(type_table)?);
                let then = Box::new(then.type_ast(type_table)?);
                let els = Box::new(els.type_ast(type_table)?);
                ExprKind::If { cond, then, els }
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let lhs = lhs.type_ast(type_table)?;
                let rhs = rhs.type_ast(type_table)?;
                ExprKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }
            ExprKind::Match { target, arms } => {
                let target = target.type_ast(type_table)?;
                let arms = arms
                    .into_iter()
                    .map(
                        |MatchArm {
                             pattern,
                             cond,
                             body,
                         }| {
                            let cond = cond
                                .map(|c| c.type_ast(type_table))
                                .transpose()?
                                .map(Box::new);
                            let body = body.type_ast(type_table)?;

                            Ok(MatchArm {
                                pattern,
                                cond,
                                body: Box::new(body),
                            })
                        },
                    )
                    .collect::<Result<Vec<_>, _>>()?;
                ExprKind::Match {
                    target: Box::new(target),
                    arms,
                }
            }
            ExprKind::StructInitializer {
                name,
                fields,
                generics,
            } => {
                let fields = fields
                    .into_iter()
                    .map(|(name, e)| {
                        let e = e.type_ast(type_table)?;
                        Ok((name, e))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                ExprKind::StructInitializer {
                    name,
                    fields,
                    generics,
                }
            }
            ExprKind::MemberAccess { target, member } => {
                let target = target.type_ast(type_table)?;
                ExprKind::MemberAccess {
                    target: Box::new(target),
                    member,
                }
            }
            ExprKind::Unit => ExprKind::Unit,
            ExprKind::Int(v) => ExprKind::Int(v),
            ExprKind::Boolean(v) => ExprKind::Boolean(v),
            ExprKind::Identifier(v) => ExprKind::Identifier(v),
            ExprKind::Char(v) => ExprKind::Char(v),
            ExprKind::Lambda(fundecl) => ExprKind::Lambda(fundecl.type_ast()?),
        };

        Ok(TypedExpr {
            node,
            ty,
            location: self.location,
        })
    }
}

pub fn type_ast(ast: Vec<Decl>) -> Result<Vec<TypedDecl>, TypeAstErr> {
    let typed = ast
        .into_iter()
        .map(|decl| decl.type_ast())
        .collect::<Result<_, _>>()?;
    Ok(typed)
}

/// Collects all variants from all enums.
/// Returns table `moduleName -> enumName -> [variantName]`
pub fn collect_enums(
    modules: &HashMap<String, TypedModule>,
) -> HashMap<String, HashMap<String, Vec<String>>> {
    let mut enum_table: HashMap<String, HashMap<String, Vec<String>>> = HashMap::new();

    for (module_name, module) in modules.iter() {
        for decl in module.decls.iter() {
            match &decl.node {
                TypedDeclKind::EnumDecl { name, variants, .. } => {
                    let variants = variants.iter().map(|v| v.name.clone()).collect();
                    enum_table
                        .entry(module_name.clone())
                        .or_insert(HashMap::new())
                        .insert(name.clone(), variants);
                }
                _ => (),
            }
        }
    }

    enum_table
}

fn get_enum_variants(enum_name: &str, variants: &HashMap<String, Vec<String>>) -> Vec<String> {
    variants.get(enum_name).unwrap_or(&vec![]).to_vec()
}

/// Extends the import list with variants of the imported enums.
fn collect_variants(
    import: Import,
    variants: &HashMap<String, HashMap<String, Vec<String>>>,
) -> Import {
    let imported = variants.get(&import.path);
    if imported.is_none() {
        return import;
    }

    let mut new_ids = vec![];
    for import in import.imported_ids {
        let variants = get_enum_variants(&import, &imported.unwrap());
        new_ids.extend(variants);
        new_ids.push(import);
    }

    Import {
        path: import.path,
        imported_ids: new_ids,
        location: import.location,
    }
}

pub fn type_modules(
    modules: HashMap<String, Module>,
) -> Result<HashMap<String, TypedModule>, LastLayerError> {
    let mut typed: HashMap<String, TypedModule> = modules
        .into_iter()
        .map(|(path, module)| {
            let typed_decls = module
                .decls
                .into_iter()
                .map(|decl| decl.type_ast())
                .collect::<Result<_, _>>()
                .map_err(|err| LastLayerError::from_fe(err, path.clone()))?;
            Ok((
                path,
                TypedModule {
                    decls: typed_decls,
                    imports: module.imports,
                },
            ))
        })
        .collect::<Result<_, _>>()?;

    // For interpreting, we need to "fake" imports. When user uses a List, he imports
    // List but actually only uses its variants in the code. We put these variant names
    // into the imports list.
    let enums = collect_enums(&typed);

    for (_, module) in typed.iter_mut() {
        module.imports = module
            .imports
            .iter()
            .map(|import| collect_variants(import.clone(), &enums))
            .collect();
    }

    Ok(typed)
}
