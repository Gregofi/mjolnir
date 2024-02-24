use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::{
    Decl, DeclKind, ExprKind, Operator, TypedDecl, TypedDeclKind, TypedExpr, TypedStmt,
    TypedStmtKind, TypedVarDecl, VarDecl,
};
use crate::ast::{Expr, Stmt};
use crate::frontend::types::{BuiltInType, FunctionType, Type};
use crate::frontend::utils::TypedIdentifier;
use anyhow::{Context, Result};

// TODO: Why we save this and not whole typed Decl?
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
        types.insert("Bool".to_string(), Type::BuiltIn(BuiltInType::Bool).into());
        types.insert(
            "String".to_string(),
            Type::BuiltIn(BuiltInType::String).into(),
        );
        types
    }

    fn get_int(&self) -> Rc<Type> {
        self.types.get("Int").unwrap().clone()
    }

    fn get_bool(&self) -> Rc<Type> {
        self.types.get("Bool").unwrap().clone()
    }

    fn type_binary(&self, left: &Type, right: &Type, op: &Operator) -> Result<Rc<Type>> {
        let arith_operators = [Operator::Add, Operator::Sub, Operator::Mul, Operator::Div];
        let logical_operators = [
            Operator::Less,
            Operator::Greater,
            Operator::LessEqual,
            Operator::GreaterEqual,
            Operator::Equal,
            Operator::Neq,
        ];
        match (left, right, op) {
            (Type::BuiltIn(BuiltInType::Int), Type::BuiltIn(BuiltInType::Int), op)
                if arith_operators.contains(op) =>
            {
                Ok(Type::get_int())
            }
            (Type::BuiltIn(BuiltInType::Int), Type::BuiltIn(BuiltInType::Int), op)
                if logical_operators.contains(op) =>
            {
                Ok(Type::get_bool())
            }
            _ => Err(anyhow::anyhow!(
                "Binary operation not supported for types: {} and {}",
                left,
                right
            )),
        }
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

pub fn semantic_analysis(ast: &Vec<Decl>) -> Result<HashMap<String, TypedDecl>> {
    let mut symbols = SymbolTable::<IdentInfo>::new();
    symbols.push();

    for decl in ast {
        prepare_decl(&decl, &mut symbols)?;
    }

    for decl in ast {
        analyse_decl(decl, &mut symbols)?;
    }

    Ok(symbols.decls)
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
                    let args_types = typed_args
                        .iter()
                        .map(|arg| arg.ty.clone())
                        .collect::<Vec<_>>();
                    if ty.check_args(&*args_types) {
                        Ok(ty.return_type.clone())
                    } else {
                        return Err(anyhow::anyhow!(
                            "Function call arguments do not match function signature"
                        ));
                    }
                }
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
        }
        ExprKind::If { cond, then, els } => {
            let cond_typed = analyse_expr(cond, env)?;
            if !cond_typed.ty.is_bool() {
                return Err(anyhow::anyhow!(
                    "If condition must be of type Bool, found: {}",
                    cond_typed.ty
                ));
            }
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
        ExprKind::Binary { op, lhs, rhs } => {
            let lhs_typed = analyse_expr(lhs, env)?;
            let rhs_typed = analyse_expr(rhs, env)?;
            let ty = env.type_binary(&lhs_typed.ty, &rhs_typed.ty, op)?;
            if lhs_typed.ty.is_same(&rhs_typed.ty) {
                Ok(TypedExpr {
                    node: ExprKind::Binary {
                        op: *op,
                        lhs: Box::new(lhs_typed),
                        rhs: Box::new(rhs_typed),
                    },
                    location: ast.location.clone(),
                    ty,
                })
            } else {
                Err(anyhow::anyhow!(
                    "Binary operands have different types: {} and {}",
                    lhs_typed.ty,
                    rhs_typed.ty
                ))
            }
        }
        ExprKind::Boolean(b) => Ok(TypedExpr {
            node: ExprKind::Boolean(*b),
            location: ast.location.clone(),
            ty: env.get_bool(),
        }),
    }
}

fn type_var_decl(decl: &VarDecl, env: &mut SymbolTable<IdentInfo>) -> Result<TypedVarDecl> {
    let typed_value = analyse_expr(&decl.value, env)?;
    let resulting_type = match &decl.ty {
        Some(ty) => {
            let type_ = env
                .get_type(ty)
                .with_context(|| format!("Type '{}' not declared", ty))?;
            if !typed_value.ty.is_same(type_) {
                return Err(anyhow::anyhow!(
                    "Declared type '{}' does not match value type '{}'",
                    type_,
                    typed_value.ty
                ));
            } else {
                type_.clone()
            }
        }
        None => typed_value.ty.clone(),
    };

    Ok(TypedVarDecl {
        name: decl.name.clone(),
        value: Box::new(typed_value),
    })
}

/// Prepare global declarations (which must be explicitely typed) as types and
/// identifiers. This prevents forward references and allows recursive functions.
fn prepare_decl(ast: &Decl, env: &mut SymbolTable<IdentInfo>) -> Result<()> {
    match &ast.node {
        DeclKind::FunDecl {
            name,
            parameters,
            return_type,
            ..
        } => {
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
            }

            let return_type_str = return_type
                .as_ref()
                .expect("Function must have explicit return type");
            let return_type = env
                .get_type(&return_type_str)
                .with_context(|| format!("Return type '{}' not declared", return_type_str))?;
            let funtype = Rc::new(Type::FunctionType(Box::new(FunctionType {
                parameters: typed_params,
                return_type: return_type.clone(),
            })));
            env.insert(name.clone(), IdentInfo { ty: funtype });
        }
        _ => todo!(),
    };
    Ok(())
}

fn analyse_decl(ast: &Decl, env: &mut SymbolTable<IdentInfo>) -> Result<()> {
    match &ast.node {
        DeclKind::FunDecl { name, body, .. } => {
            let typed = env
                .get(name)
                .expect("Function must be prepared by prepare_decl; Compiler bug")
                .ty
                .clone();
            let typed = typed.as_function().context("Not a function")?;

            env.push();
            for param in &typed.parameters {
                env.insert(
                    param.name.clone(),
                    IdentInfo {
                        ty: param.ty.clone(),
                    },
                );
            }

            let typed_expr = analyse_expr(&body, env)?;

            env.pop();

            let decl = if typed_expr.ty.is_same(&typed.return_type) {
                Ok(TypedDecl {
                    node: TypedDeclKind::FunDecl {
                        name: name.clone(),
                        parameters: typed.parameters.clone(),
                        return_type: typed.return_type.clone(),
                        body: Box::new(typed_expr),
                    },
                    location: ast.location.clone(),
                })
            } else {
                Err(anyhow::anyhow!(
                    "Return type '{}' does not match function return type",
                    typed.return_type
                ))
            }?;
            env.add_decl(name.clone(), decl);
        }
        DeclKind::StructDecl { name, fields } => todo!(),
        DeclKind::EnumDecl { name, variants } => todo!(),
        DeclKind::TraitDecl { name, methods } => todo!(),
        DeclKind::VarDecl(var_decl) => {
            let typed_decl = type_var_decl(var_decl, env)?;

            // TODO: This may not be enough with global variables.
            // we will see when we implement interpreting.
            env.insert(
                var_decl.name.clone(),
                IdentInfo {
                    ty: typed_decl.value.ty.clone(),
                },
            );
        }
    }
    Ok(())
}

fn analyse_stmt(ast: &Stmt, env: &mut SymbolTable<IdentInfo>) -> Result<TypedStmt> {
    let node = match &ast.node {
        crate::ast::StmtKind::VarDecl(var_decl) => {
            let typed_decl = type_var_decl(var_decl, env)?;
            env.insert(
                var_decl.name.clone(),
                IdentInfo {
                    ty: typed_decl.value.ty.clone(),
                },
            );
            TypedStmtKind::VarDecl(typed_decl)
        }
    };

    Ok(TypedStmt {
        node,
        location: ast.location.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    // TODO: ??? ;)
    use crate::frontend::parser::parse_ast;

    #[test]
    fn test_semantic_analysis() {
        let ast = parse_ast("fn foo(x: Int): Int = x").unwrap();
        semantic_analysis(&ast).unwrap();

        let ast = parse_ast("fn foo(x: Int): Int = y").unwrap();
        assert!(semantic_analysis(&ast).is_err());

        let ast = parse_ast("fn foo(x: Int): Int = foo(5)").unwrap();
        assert!(semantic_analysis(&ast).is_ok());
    }

    #[test]
    fn test_sa_ifs() {
        let ast = parse_ast("fn foo(x: Int): Int = if true { 1 } else { 2 }").unwrap();
        assert!(semantic_analysis(&ast).is_ok());

        let ast = parse_ast("fn foo(x: Int): Int = if 1 { 2 } else { 3 }").unwrap();
        assert!(semantic_analysis(&ast).is_err());

        let ast = parse_ast("fn foo(x: Int): Int = if true { 1 } else { true }").unwrap();
        assert!(semantic_analysis(&ast).is_err());
    }

    #[test]
    fn test_binary_expr() {
        let ast = parse_ast("fn foo(x: Int): Int = x + 1").unwrap();
        assert!(semantic_analysis(&ast).is_ok());

        let ast = parse_ast("fn foo(x: Int): Bool = x + 1 == 2").unwrap();
        assert!(semantic_analysis(&ast).is_ok());

        let ast = parse_ast("fn foo(x: Int): Int = x + 1 == 2").unwrap();
        assert!(semantic_analysis(&ast).is_err());
    }

    #[test]
    fn test_compound_expr() {
        let ast = parse_ast("fn foo(x: Int): Int = { let y = 5; y }").unwrap();
        assert!(semantic_analysis(&ast).is_ok());

        let ast = parse_ast("fn foo(x: Int): Int = { let y = 5; y + 1 }").unwrap();
        assert!(semantic_analysis(&ast).is_ok());

        let ast = parse_ast("fn foo(x: Int): Int = { let y = true; y + 1 }").unwrap();
        assert!(semantic_analysis(&ast).is_err());
    }

    #[test]
    fn test_functions() {
        let ast = parse_ast("fn bar(x: Int): Int = foo(x)  fn foo(x: Int): Int = x").unwrap();
        assert!(semantic_analysis(&ast).is_ok());

        // recursive fun
        let ast =
            parse_ast("fn fact(n: Int): Int = if n == 0 { 1 } else { n * fact(n - 1) }").unwrap();
        assert!(semantic_analysis(&ast).is_ok());
    }
}
