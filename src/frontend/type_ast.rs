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

use crate::ast::*;
use crate::frontend::types::TypeInfo;

use super::type_inference::{Constructor, Type as InferredType};
use super::types::{
    BuiltInType, EnumType, EnumVariantType, FunctionType, InstantiatedType, Parameter, StructType,
    TypeKind,
};
use super::utils::{StronglyTypedIdentifier, TypedIdentifier, WrittenType};

#[derive(Debug, Clone)]
pub enum TypeAstError {
    NonExistingType(String),
    #[allow(dead_code)]
    Untyped(String),
}

impl Display for TypeAstError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            TypeAstError::NonExistingType(msg) => write!(f, "{}", msg),
            TypeAstError::Untyped(msg) => write!(f, "{}", msg),
        }
    }
}

impl WrittenType {
    fn to_instantiated_type(&self) -> Result<InstantiatedType, TypeAstError> {
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
    fn to_instantiated_type(&self) -> Result<InstantiatedType, TypeAstError> {
        match self {
            InferredType::TypeVar(_) => Err(TypeAstError::NonExistingType(
                "E0001 (Compiler bug): Cannot have type variables when typing AST".to_string(),
            )),
            InferredType::Constructor(Constructor { name, type_vec }) => {
                let generics = type_vec
                    .iter()
                    .map(|arg| arg.to_instantiated_type())
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(InstantiatedType {
                    ty: name.clone(),
                    generics,
                })
            }
        }
    }
}

impl Decl {
    pub fn type_ast(self) -> Result<TypedDecl, TypeAstError> {
        let typed_kind = match self.node {
            DeclKind::FunDecl {
                name,
                inferred_parameters,
                inferred_return_type,
                parameters,
                body,
                ..
            } => {
                let parameters = inferred_parameters
                    .expect("E0002 (Compiler bug): Type inference must be done at this point")
                    .into_iter()
                    .zip(parameters)
                    .map(|(ty, param)| {
                        let ty = ty.to_instantiated_type()?;
                        Ok(TypedIdentifier {
                            name: param.name,
                            ty,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let return_type = inferred_return_type
                    .expect("E0003 (Compiler bug): Type inference must be done at this point")
                    .to_instantiated_type()?;
                let body = body.type_ast(&HashMap::new())?;
                TypedDeclKind::FunDecl {
                    name,
                    parameters,
                    return_type,
                    body: Box::new(body),
                }
            }
            DeclKind::StructDecl { name, fields, .. } => {
                let fields = fields
                    .into_iter()
                    .map(|StronglyTypedIdentifier { name, ty }| {
                        let ty = ty.to_instantiated_type()?;
                        Ok(TypedIdentifier { name, ty })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                TypedDeclKind::StructDecl { name, fields }
            }
            DeclKind::EnumDecl { name, variants, .. } => TypedDeclKind::EnumDecl { name, variants },
            DeclKind::TraitDecl { .. } => todo!(),
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
    ) -> Result<TypedStmt, TypeAstError> {
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
    ) -> Result<TypedExpr, TypeAstError> {
        let ty = if let Some(ty) = &self.inferred_ty {
            ty.to_instantiated_type()?
        } else {
            return Err(TypeAstError::NonExistingType(
                "E0002 (Compiler bug): Cannot type AST without inferred types".to_string(),
            ));
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
        };

        Ok(TypedExpr {
            node,
            ty,
            location: self.location,
        })
    }
}

/// Collects all type declarations and returns a table from type identifiers to TypeInfo. Uses the
/// inferred types for functions, otherwise the types used are the ones from the AST.
///
/// @skip_functions: If true, functions will not be added to the type table. This means that
/// the function can be used before type inference.
pub fn collect_decls(
    decls: &Vec<Decl>,
    skip_functions: bool,
) -> Result<HashMap<String, TypeInfo>, TypeAstError> {
    let mut type_table = HashMap::new();

    type_table.insert(
        "Int".to_string(),
        TypeInfo {
            kind: TypeKind::BuiltIn(BuiltInType::Int),
            generics: vec![],
        },
    );

    type_table.insert(
        "Unit".to_string(),
        TypeInfo {
            kind: TypeKind::BuiltIn(BuiltInType::Unit),
            generics: vec![],
        },
    );

    type_table.insert(
        "Bool".to_string(),
        TypeInfo {
            kind: TypeKind::BuiltIn(BuiltInType::Bool),
            generics: vec![],
        },
    );

    type_table.insert(
        "String".to_string(),
        TypeInfo {
            kind: TypeKind::BuiltIn(BuiltInType::String),
            generics: vec![],
        },
    );

    for decl in decls {
        match &decl.node {
            DeclKind::FunDecl {
                name,
                generics,
                inferred_parameters,
                inferred_return_type,
                ..
            } => {
                if skip_functions {
                    continue;
                }
                let parameters = inferred_parameters
                    .as_ref()
                    .ok_or(TypeAstError::Untyped(
                        "Type inference must be done at this point".to_string(),
                    ))?
                    .iter()
                    .map(|ty| {
                        let ty = ty.to_instantiated_type()?;
                        Ok(Parameter {
                            name: name.clone(),
                            ty,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let return_type = inferred_return_type
                    .clone()
                    .expect("Return type of a function must be specified explicitly")
                    .to_instantiated_type()?;
                let function_type = FunctionType {
                    parameters,
                    return_type,
                };
                type_table.insert(
                    name.clone(),
                    TypeInfo {
                        kind: TypeKind::Function(function_type),
                        generics: generics.clone(),
                    },
                );
            }
            DeclKind::StructDecl {
                name,
                generics,
                fields,
            } => {
                let fields = fields.iter().try_fold(
                    HashMap::new(),
                    |mut acc, StronglyTypedIdentifier { name, ty }| {
                        let ty = ty.to_instantiated_type()?;
                        acc.insert(name.clone(), ty);
                        Ok(acc)
                    },
                )?;
                let struct_type = StructType {
                    name: name.clone(),
                    fields,
                };
                type_table.insert(
                    name.clone(),
                    TypeInfo {
                        kind: TypeKind::Struct(struct_type),
                        generics: generics.clone(),
                    },
                );
            }
            DeclKind::EnumDecl {
                name,
                variants,
                generics,
            } => {
                let variants = variants
                    .iter()
                    .map(|variant| {
                        let fields = variant
                            .fields
                            .clone()
                            .into_iter()
                            .map(|field| field.to_instantiated_type())
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok(EnumVariantType {
                            name: variant.name.clone(),
                            fields,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let enum_type = EnumType {
                    name: name.clone(),
                    variants,
                };
                type_table.insert(
                    name.clone(),
                    TypeInfo {
                        kind: TypeKind::Enum(enum_type),
                        generics: generics.clone(),
                    },
                );
            }
            DeclKind::TraitDecl { .. } => todo!(),
        }
    }
    Ok(type_table)
}

pub fn type_ast(ast: Vec<Decl>) -> Result<Vec<TypedDecl>, TypeAstError> {
    let typed = ast
        .into_iter()
        .map(|decl| decl.type_ast())
        .collect::<Result<_, _>>()?;
    Ok(typed)
}
