use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::{
    Decl, DeclKind, Expr, ExprKind, MatchArm, Operator, Pattern, Stmt, StmtKind, TypedDecl,
    TypedDeclKind, TypedExpr, TypedStmt, TypedStmtKind, TypedVarDecl, VarDecl,
};
use crate::frontend::types::{BuiltInType, EnumVariantType, FunctionType, Type};
use crate::frontend::utils::TypedIdentifier;
use anyhow::{Context, Result};

use super::types::StructType;
use super::types::{EnumType, Parameter};

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
        types.insert("Int".to_string(), Type::get_int());
        types.insert("Bool".to_string(), Type::get_bool());
        types.insert("Unit".to_string(), Type::get_unit());
        types.insert(
            "String".to_string(),
            Type::BuiltIn(BuiltInType::String).into(),
        );
        types
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

    pub fn get_types(&self, names: &[String]) -> Result<Vec<Rc<Type>>> {
        names
            .iter()
            .map(|name| {
                let ty = self
                    .get_type(name)
                    .with_context(|| format!("Unknown type '{}'", name))?
                    .clone();
                Ok(ty)
            })
            .collect::<Result<Vec<_>>>()
    }

    pub fn insert_type(&mut self, name: String, value: Rc<Type>) {
        self.types.insert(name, value);
    }

    pub fn add_decl(&mut self, name: String, decl: TypedDecl) {
        self.decls.insert(name, decl);
    }
}

impl StructType {
    fn get_member_type(
        &self,
        member: &str,
        env: &SymbolTable<IdentInfo>,
    ) -> Option<Result<Rc<Type>>> {
        self.fields.get(member).map(|ty| -> Result<_> {
            let ty = env
                .get_type(ty)
                .with_context(|| format!("Unknown type '{}' for member '{}'", ty, member))?
                .clone();
            Ok(ty)
        })
    }
}

impl FunctionType {
    fn get_param_types(&self, env: &SymbolTable<IdentInfo>) -> Result<Vec<Rc<Type>>> {
        self.parameters
            .iter()
            .map(|param| {
                let ty = env
                    .get_type(&param.ty)
                    .with_context(|| {
                        format!("Unknown type '{}' for parameter '{}'", param.ty, param.name)
                    })?
                    .clone();
                Ok(ty)
            })
            .collect::<Result<Vec<_>>>()
    }

    fn check_args(&self, env: &SymbolTable<IdentInfo>, arg_types: &[Rc<Type>]) -> bool {
        if self.parameters.len() != arg_types.len() {
            false
        } else {
            let param_types = self.get_param_types(env).unwrap();
            arg_types
                .iter()
                .zip(param_types.iter())
                .all(|(arg, param)| arg.is_same(param))
        }
    }
}

fn prepare_native_functions(env: &mut SymbolTable<IdentInfo>) {
    let natives = crate::backend::ast_interpreter::native_functions::get_native_functions();
    for native in natives {
        env.insert(
            native.name.clone(),
            IdentInfo {
                ty: native.ty.wrap(),
            },
        );
    }
}

pub fn semantic_analysis(ast: &Vec<Decl>) -> Result<HashMap<String, TypedDecl>> {
    let mut symbols = SymbolTable::<IdentInfo>::new();
    symbols.push();

    prepare_native_functions(&mut symbols);

    for decl in ast {
        prepare_decl(&decl, &mut symbols)?;
    }

    for decl in ast {
        analyse_decl(decl, &mut symbols)?;
    }

    Ok(symbols.decls)
}

fn analyse_match_arm(
    target: &Rc<Type>,
    pattern: &Pattern,
    env: &SymbolTable<IdentInfo>,
) -> Result<Vec<TypedIdentifier>> {
    println!("Analyse match arm: {} <=> {:?}", target, pattern);
    match (target.as_ref(), pattern) {
        (_, Pattern::Wildcard) => Ok(vec![]),
        (_, Pattern::Identifier(name)) => Ok(vec![TypedIdentifier {
            name: name.clone(),
            ty: target.clone(),
        }]),
        (Type::BuiltIn(BuiltInType::Int), Pattern::Int(_)) => Ok(vec![]),
        (Type::BuiltIn(BuiltInType::Bool), Pattern::Boolean(_)) => Ok(vec![]),
        (Type::BuiltIn(BuiltInType::String), Pattern::String(_)) => Ok(vec![]),
        (
            Type::Struct(struct_type),
            Pattern::Struct {
                name: pattern_name,
                fields: pattern_fields,
            },
        ) => {
            if &struct_type.name != pattern_name {
                return Err(anyhow::anyhow!(
                    "Pattern '{}' does not match target type '{}'",
                    pattern,
                    target,
                ));
            }
            let typed_fields = pattern_fields
                .iter()
                .map(|name| {
                    let ty = struct_type
                        .get_member_type(name, env)
                        .with_context(|| format!("Unknown member '{}'", name))??;
                    Ok(TypedIdentifier {
                        name: name.clone(),
                        ty,
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            Ok(typed_fields)
        }
        (
            Type::Enum(enum_type),
            Pattern::Enum {
                name: variant_pattern,
                patterns,
            },
        ) => {
            let variant_type = enum_type
                .variants
                .iter()
                .find(|variant| &variant.name == variant_pattern)
                .with_context(|| {
                    format!(
                        "Variant '{}' does not exist in '{}'",
                        variant_pattern, enum_type.name
                    )
                })?;
            let item_types = env.get_types(&variant_type.fields)?;
            let identifiers = patterns
                .iter()
                .zip(item_types.iter())
                .map(|(pattern, ty)| analyse_match_arm(ty, pattern, env))
                .collect::<Result<Vec<_>>>()?
                .into_iter()
                .flatten()
                .collect();

            Ok(identifiers)
        }
        _ => Err(anyhow::anyhow!(
            "Pattern '{}' does not match target type '{}'",
            pattern,
            target,
        )),
    }
}

fn analyse_match(
    target: &Expr,
    arms: &[MatchArm<Expr>],
    env: &mut SymbolTable<IdentInfo>,
) -> Result<TypedExpr> {
    let target = analyse_expr(target, env)?;

    // Check that all patterns of the arms are type correct
    // i.e. that if target is Enum Foo that pattern is not Int
    // but only variants of Foo or wildcard.
    let typed_arms = arms
        .iter()
        .map(|arm| -> Result<MatchArm<TypedExpr>> {
            let identifiers = analyse_match_arm(&target.ty, &arm.pattern, env)?;
            env.push();
            for id in identifiers {
                println!("add id: {}", id.name);
                env.insert(id.name, IdentInfo { ty: id.ty });
            }
            let typed_body = analyse_expr(&arm.body, env)?;

            let typed_cond = arm
                .cond
                .as_ref()
                .map(|cond| {
                    let typed_cond = analyse_expr(&*cond, env)?;
                    if !typed_cond.ty.is_bool() {
                        Err(anyhow::anyhow!(
                            "Match arm condition must be of type Bool, found: {}",
                            typed_cond.ty
                        ))
                    } else {
                        Ok(typed_cond)
                    }
                })
                .map_or(Ok(None), |res| res.map(Some))?;
            env.pop();
            Ok(MatchArm {
                pattern: arm.pattern.clone(),
                cond: typed_cond.map(|c| Box::new(c)),
                body: Box::new(typed_body),
            })
        })
        .collect::<Result<Vec<_>>>()?;

    // Check that all arms have the same return type.
    let first = typed_arms.first().unwrap().body.ty.clone();
    if typed_arms
        .iter()
        .all(|arm_type| arm_type.body.ty.is_same(&first))
    {
        let location = target.location.clone();
        Ok(TypedExpr {
            node: ExprKind::Match {
                target: Box::new(target),
                arms: typed_arms,
            },
            location,
            ty: first.clone(),
        })
    } else {
        Err(anyhow::anyhow!("Match arms have different types"))
    }
}

fn analyse_expr(ast: &Expr, env: &mut SymbolTable<IdentInfo>) -> Result<TypedExpr> {
    match &ast.node {
        ExprKind::Unit => Ok(TypedExpr {
            node: ExprKind::Unit,
            location: ast.location.clone(),
            ty: Type::get_unit(),
        }),
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
            let typed_stmts = stmts
                .iter()
                .map(|stmt| analyse_stmt(stmt, env))
                .collect::<Result<Vec<_>>>()?;
            let final_expr = analyse_expr(expr, env)?;
            Ok(TypedExpr {
                node: ExprKind::Compound(typed_stmts, Box::new(final_expr.clone())),
                location: ast.location.clone(),
                ty: final_expr.ty,
            })
        }
        ExprKind::FunCall { target, args } => {
            let typed_target = analyse_expr(target, env)?;
            let typed_args = args
                .iter()
                .map(|arg| analyse_expr(arg, env))
                .collect::<Result<Vec<_>>>()?;

            let fun_ty = match typed_target.ty.as_ref() {
                Type::FunctionType(ty) => ty,
                _ => Err(anyhow::anyhow!(
                    "Target of function call is not a function: {}",
                    typed_target.ty
                ))?,
            };

            let args_types = typed_args
                .iter()
                .map(|arg| arg.ty.clone())
                .collect::<Vec<_>>();

            if !fun_ty.check_args(env, &*args_types) {
                return Err(anyhow::anyhow!(
                    "Function call arguments do not match function signature"
                ));
            }

            let fun_ret_type = env
                .get_type(&fun_ty.return_type)
                .expect("E1000 Compiler bug; unknown return type.")
                .clone();

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
            ty: Type::get_bool(),
        }),
        ExprKind::Match { target, arms } => analyse_match(target, arms, env),
        ExprKind::StructInitializer { name, fields } => {
            let fields = fields
                .iter()
                .try_fold(vec![], |mut acc, (name, expr)| -> Result<_> {
                    let typed = analyse_expr(expr, env)?;
                    acc.push((name.clone(), typed));
                    Ok(acc)
                })?;
            Ok(TypedExpr {
                node: ExprKind::StructInitializer {
                    name: name.clone(),
                    fields,
                },
                location: ast.location.clone(),
                ty: env
                    .get_type(name)
                    .with_context(|| format!("Unknown struct type {}", name))?
                    .clone(),
            })
        }
        ExprKind::MemberAccess { target, member } => {
            let target = analyse_expr(target, env)?;
            let ty = match target.ty.as_ref() {
                Type::Struct(struct_type) => struct_type
                    .get_member_type(member, env)
                    .with_context(|| format!("Unknown member {}", member))?,
                _ => Err(anyhow::anyhow!(
                    "Member access on non-struct type: {}",
                    target.ty
                )),
            }?;

            Ok(TypedExpr {
                node: ExprKind::MemberAccess {
                    target: Box::new(target),
                    member: member.clone(),
                },
                location: ast.location.clone(),
                ty,
            })
        }
    }
}

fn type_var_decl(decl: &VarDecl, env: &mut SymbolTable<IdentInfo>) -> Result<TypedVarDecl> {
    let typed_value = analyse_expr(&decl.value, env)?;
    match &decl.ty {
        Some(ty) => {
            let type_ = env
                .get_type(ty)
                .with_context(|| format!("Type '{}' not declared", ty))?;
            if !typed_value.ty.is_same(type_) {
                Err(anyhow::anyhow!(
                    "Declared type '{}' does not match value type '{}'",
                    type_,
                    typed_value.ty
                ))
            } else {
                Ok(())
            }
        }
        None => Ok(()),
    }?;

    Ok(TypedVarDecl {
        name: decl.name.clone(),
        value: Box::new(typed_value),
    })
}

/// Prepare global declarations (which must be explicitely typed) as types and
/// identifiers. This prevents forward references and allows recursive functions.
/// This does not perform analysis on the declarations body.
/// In structs, when the type is not known in the SymbolTable, it is added as
/// untyped (string name). The actual type is then searched in the SymbolTable
/// in semantic_analysis.
fn prepare_decl(ast: &Decl, env: &mut SymbolTable<IdentInfo>) -> Result<()> {
    match &ast.node {
        DeclKind::FunDecl {
            name,
            parameters,
            return_type,
            ..
        } => {
            let parameters = parameters
                .iter()
                .map(|param| -> Result<_> {
                    let ty = param
                        .ty
                        .clone()
                        .context("Parameters must by typed explicitely")?;
                    Ok(Parameter {
                        name: param.name.clone(),
                        ty,
                    })
                })
                .collect::<Result<_>>()?;
            let return_type = return_type
                .as_ref()
                .context("Function must have explicit return type")?
                .clone();
            let funtype = Rc::new(Type::FunctionType(Box::new(FunctionType {
                parameters,
                return_type,
            })));
            env.insert(name.clone(), IdentInfo { ty: funtype });
        }
        DeclKind::StructDecl { name, fields } => {
            let fields = fields.iter().fold(HashMap::new(), |mut acc, item| {
                acc.insert(item.name.clone(), item.ty.clone());
                acc
            });
            let struct_type = Rc::new(Type::Struct(StructType {
                name: name.clone(),
                fields,
            }));
            env.insert_type(name.clone(), struct_type.clone());
        }
        // Enum is most fun, because the constructor of variants that are
        // written as `enum List { Cons(Int, List), Nil }` have to be
        // transformed into free functions, so that you can do things like
        // lst.fold(Nil, (elem, acc) => Cons(elem, acc))
        DeclKind::EnumDecl {
            name: enum_name,
            variants,
        } => {
            let mut variants_mapped = vec![];
            // Collect variant type names, also create the corresponding costructors.
            for variant in variants {
                let variant_fields: Vec<_> = variant.fields.iter().map(|f| f.ty.clone()).collect();
                let parameters = variant_fields
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| Parameter {
                        name: i.to_string(),
                        ty: ty.clone(),
                    })
                    .collect();
                let funtype = Rc::new(Type::FunctionType(Box::new(FunctionType {
                    parameters,
                    return_type: enum_name.clone(),
                })));
                env.insert(variant.name.clone(), IdentInfo { ty: funtype });
                variants_mapped.push(EnumVariantType {
                    name: variant.name.clone(),
                    fields: variant_fields,
                });
            }

            let enum_type = Rc::new(Type::Enum(EnumType {
                name: enum_name.clone(),
                variants: variants_mapped,
            }));
            env.insert_type(enum_name.clone(), enum_type.clone());
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
            let return_ty = env.get_type(&typed.return_type).unwrap().clone();

            env.push();
            let mut typed_params = vec![];
            for param in &typed.parameters {
                let param_type = env
                    .get_type(&param.ty)
                    .with_context(|| {
                        format!("Unknown type '{}' for parameter '{}'", param.ty, param.name)
                    })?
                    .clone();
                env.insert(
                    param.name.clone(),
                    IdentInfo {
                        ty: param_type.clone(),
                    },
                );
                typed_params.push(TypedIdentifier {
                    name: param.name.clone(),
                    ty: param_type,
                });
            }

            let typed_expr = analyse_expr(&body, env)?;

            env.pop();

            let decl = if typed_expr.ty.is_same(&return_ty) {
                Ok(TypedDecl {
                    node: TypedDeclKind::FunDecl {
                        name: name.clone(),
                        parameters: typed_params,
                        return_type: return_ty,
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
        DeclKind::StructDecl { .. } => {
            // We ignore structs here, because they are already prepared in
            // prepare_decl. TODO: methods?
        }
        DeclKind::EnumDecl { variants, .. } => {
            // TODO: Methods
            for variant in variants {
                env.add_decl(
                    variant.name.clone(),
                    TypedDecl {
                        node: TypedDeclKind::VariantConstructor {
                            name: variant.name.clone(),
                            fields_count: variant.fields.len(),
                        },
                        location: ast.location.clone(),
                    },
                )
            }
            ()
        }
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
        StmtKind::VarDecl(var_decl) => {
            let typed_decl = type_var_decl(var_decl, env)?;
            env.insert(
                var_decl.name.clone(),
                IdentInfo {
                    ty: typed_decl.value.ty.clone(),
                },
            );
            TypedStmtKind::VarDecl(typed_decl)
        }
        StmtKind::Expr(expr) => {
            let typed_expr = analyse_expr(expr, env)?;
            TypedStmtKind::Expr(typed_expr)
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

    #[test]
    fn test_structs() {
        let ast = parse_ast("struct Foo { x: Int }  fn foo(x: Int): Int = &Foo{x: 2}.x").unwrap();
        assert!(semantic_analysis(&ast).is_ok());

        let ast = parse_ast("struct Foo { x: Int }  fn foo(x: Int): Foo = &Foo{x: 2}").unwrap();
        assert!(semantic_analysis(&ast).is_ok());

        let ast = parse_ast("struct Foo { x: Int }  fn foo(x: Int): Foo = &Foo{x: 2}.x").unwrap();
        assert!(semantic_analysis(&ast).is_err());
    }

    #[test]
    fn test_enums() {
        let ast = parse_ast("enum Foo { A, B }  fn foo(x: Int): Foo = A()").unwrap();
        assert!(semantic_analysis(&ast).is_ok());

        let ast = parse_ast("enum Foo { A, B }  fn foo(x: Int): Foo = x").unwrap();
        assert!(semantic_analysis(&ast).is_err());
    }

    #[test]
    fn test_match_primitives() {
        let ast = parse_ast("fn foo(): Int = match 1 { 1 => 2, 2 => 3 }").unwrap();
        assert!(semantic_analysis(&ast).is_ok());

        let ast = parse_ast("fn foo(): Int = match 1 { 1 => 2, 2 => true }").unwrap();
        assert!(semantic_analysis(&ast).is_err());

        let ast = parse_ast("fn foo(): Int = match 1 { true => 2 }").unwrap();
        assert!(semantic_analysis(&ast).is_err());

        let ast = parse_ast("fn foo(): Bool = match 1 { 1 => true, 2 => false }").unwrap();
        assert!(semantic_analysis(&ast).is_ok());
    }

    #[test]
    fn test_match_enums() {
        let ast = parse_ast("enum Foo { A, B(Int) }  fn foo(x: Foo): Int = match x { A() => 1, B(value) => value + 1 }").unwrap();
        semantic_analysis(&ast).unwrap();
        assert!(semantic_analysis(&ast).is_ok());
    }
}
