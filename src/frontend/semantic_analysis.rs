use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::{Decl, DeclKind, ExprKind, TypedExpr, TypedDeclKind, TypedDecl, TypedIdentifier};
use crate::ast::{Expr, Stmt};
use crate::frontend::types::{BuiltInType, Type, FunctionType};
use anyhow::{Context, Result};

struct IdentInfo {
    ty: Rc<Type>,
}

pub struct Environment<T> {
    identifiers: HashMap<String, T>,
}

impl<T> Environment<T> {
    fn new() -> Self {
        Self {
            identifiers: HashMap::new(),
        }
    }
}

pub struct SymbolTable<T> {
    pub identifiers: Vec<Environment<T>>,
    types: HashMap<String, Rc<Type>>,
    decls: HashMap<String, TypedDecl>,
}

impl<T> SymbolTable<T> {
    fn predefined_types() -> HashMap<String, Rc<Type>> {
        let mut types = HashMap::new();
        types.insert("Int".to_string(), Type::BuiltIn(BuiltInType::Int).into());
        types.insert(
            "String".to_string(),
            Type::BuiltIn(BuiltInType::Bool).into(),
        );
        types.insert(
            "Bool".to_string(),
            Type::BuiltIn(BuiltInType::String).into(),
        );
        types
    }

    pub fn new() -> Self {
        Self {
            identifiers: Vec::new(),
            types: Self::predefined_types(),
            decls: HashMap::new(),
        }
    }

    pub fn push(&mut self) {
        self.identifiers.push(Environment::new());
    }

    pub fn pop(&mut self) {
        self.identifiers.pop();
    }

    pub fn insert(&mut self, name: String, value: T) {
        self.identifiers
            .last_mut()
            .unwrap()
            .identifiers
            .insert(name, value);
    }

    pub fn get(&self, name: &str) -> Option<&T> {
        self.identifiers
            .iter()
            .rev()
            .find_map(|env| env.identifiers.get(name))
    }

    pub fn get_type(&self, name: &str) -> Option<&Rc<Type>> {
        self.types.get(name)
    }

    pub fn insert_type(&mut self, name: String, value: Rc<Type>) {
        self.types.insert(name, value);
    }

    pub fn add_decl(&mut self, name: String, decl: TypedDecl) {
        self.decls.insert(name, decl);
    }
}

fn semantic_analysis(ast: &Vec<Decl>) -> Result<()> {
    let mut symbols = SymbolTable::<IdentInfo>::new();
    symbols.push();
    for decl in ast {
        analyse_decl(decl, &mut symbols)?;
    }
    Ok(())
}

fn analyse_expr(ast: &Expr, env: &mut SymbolTable<IdentInfo>) -> Result<TypedExpr> {
    match &ast.node {
        ExprKind::Int(v) => Ok(TypedExpr {
            node: ExprKind::Int(*v),
            location: ast.location.clone(),
            ty: env.get_type("Int").unwrap().clone(),
        }),
        ExprKind::Identifier(name) => {
            let id = env.get(name);
            match id {
                Some(id) => {
                    let ty = id.ty.clone();
                    Ok(TypedExpr {
                        node: ExprKind::Identifier(name.clone()),
                        location: ast.location.clone(),
                        ty,
                    })
                }
                None => Err(anyhow::anyhow!("Identifier '{}' not declared", name))?,
            }
        }
        ExprKind::Compound(stmts, expr) => {
            for stmt in stmts {
                analyse_stmt(stmt, env)?;
            }
            analyse_expr(expr, env)
        }
        ExprKind::FunCall { target, args } => {
            let typed_target = analyse_expr(target, env)?;
            let typed_args = args
                .iter()
                .map(|arg| analyse_expr(arg, env))
                .collect::<Result<Vec<_>>>()?;

            let fun_ret_type = match typed_target.ty.as_ref() {
                Type::FunctionType(ty) => {
                    let args_types = typed_args.iter().map(|arg| arg.ty.clone()).collect::<Vec<_>>();
                    if ty.check_args(&*args_types) {
                        Ok(ty.return_type.clone())
                    } else {
                        return Err(anyhow::anyhow!(
                            "Function call arguments do not match function signature"
                        ));
                    }
                },
                _ => Err(anyhow::anyhow!(
                    "Target of function call is not a function: {}",
                    typed_target.ty
                )),
            }?;

            Ok(TypedExpr {
                node: ExprKind::FunCall {
                    target: Box::new(typed_target),
                    args: typed_args,
                },
                location: ast.location.clone(),
                ty: fun_ret_type,
            })
        },
        ExprKind::If { cond, then, els } => {
            let cond_typed = analyse_expr(cond, env)?;
            let then_typed = analyse_expr(then, env)?;
            let els_typed = analyse_expr(els, env)?;
            let ty = then_typed.ty.clone();
            if then_typed.ty.is_same(&els_typed.ty) {
                Ok(TypedExpr {
                    node: ExprKind::If {
                        cond: Box::new(cond_typed),
                        then: Box::new(then_typed),
                        els: Box::new(els_typed),
                    },
                    location: ast.location.clone(),
                    ty,
                })
            } else {
                Err(anyhow::anyhow!(
                    "If branches have different types: {} and {}",
                    then_typed.ty,
                    els_typed.ty
                ))
            }
        }
    }
}

fn analyse_decl(ast: &Decl, env: &mut SymbolTable<IdentInfo>) -> Result<()> {
    match &ast.node {
        DeclKind::FunDecl {
            name,
            parameters,
            return_type,
            body,
        } => {
            env.push();
            let mut typed_params = vec![];
            for param in parameters {
                let param_type = param
                    .ty
                    .as_ref()
                    .expect("Function parameters must be typed explicitely");
                let ty = env
                    .get_type(param_type)
                    .with_context(|| format!("Type '{}' not declared", param_type))?;
                typed_params.push(TypedIdentifier {
                    name: param.name.clone(),
                    ty: ty.clone(),
                });
                env.insert(param.name.clone(), IdentInfo { ty: ty.clone() });
            }

            let return_type_str = return_type.as_ref().expect("Function must have explicit return type");
            let return_type = env.get_type(&return_type_str).with_context(|| {
                format!("Return type '{}' not declared", return_type_str)

            })?.clone();
            let funtype = Rc::new(Type::FunctionType(Box::new(FunctionType {
                parameters: typed_params.iter().map(|p| p.ty.clone()).collect(),
                return_type: return_type.clone(),
            })));

            env.insert_type(name.clone(), funtype.clone());
            env.insert(name.clone(), IdentInfo { ty: funtype.clone() });

            let typed_expr = analyse_expr(&body, env)?;

            env.pop();

            let decl = if typed_expr.ty.is_same(&return_type) {
                Ok(TypedDecl {
                    node: TypedDeclKind::FunDecl {
                        name: name.clone(),
                        parameters: typed_params,
                        return_type: return_type.clone(),
                        body: Box::new(typed_expr),
                    },
                    location: ast.location.clone(),
                })
            } else {
                Err(anyhow::anyhow!(
                    "Return type '{}' does not match function return type",
                    return_type
                ))
            }?;
            env.add_decl(name.clone(), decl);
        }
        DeclKind::StructDecl { name, fields } => todo!(),
        DeclKind::EnumDecl { name, variants } => todo!(),
        DeclKind::TraitDecl { name, methods } => todo!(),
    }
    Ok(())
}

fn analyse_stmt(ast: &Stmt, env: &mut SymbolTable<IdentInfo>) -> Result<Stmt> {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    // TODO: ??? ;)
    use super::super::super::parser::parse_ast;

    #[test]
    fn test_semantic_analysis() {
        let ast = parse_ast("fn foo(x: Int): Int = x").unwrap();
        semantic_analysis(&ast).unwrap();

        let ast = parse_ast("fn foo(x: Int): Int = y").unwrap();
        assert!(semantic_analysis(&ast).is_err());

        let ast = parse_ast("fn foo(x: Int): Int = x  fn bar(y: Int): Int = x").unwrap();
        assert!(semantic_analysis(&ast).is_err());

        let ast = parse_ast("fn foo(x: Int): Int = foo(5)").unwrap();
        semantic_analysis(&ast).unwrap();
    }
}
