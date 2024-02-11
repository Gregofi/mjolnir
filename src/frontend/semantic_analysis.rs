use std::collections::HashMap;

use crate::ast::{Stmt, Expr};
use anyhow::Result;
use crate::frontend::utils::SymbolTable;
use crate::ast::{ExprKind, StmtKind};

/**
 * Does semantic analysis of the AST, checks that
 * - are identifiers are declared.
 * - identifier names are not duplicated.
 * - assignments only happen to lvalues.    TODO: This should not even be possible on grammar
 * level.
 */
fn semantic_analysis(ast: &Stmt) -> Result<()> {
    let mut symbols = SymbolTable::<()>::new();
    symbols.push();
    analyse_stmt(ast, &mut symbols)
}

fn analyse_expr(ast: &Expr, env: &SymbolTable<()>) -> Result<()> {
    match &ast.node {
        ExprKind::Int(_) => Ok(()),
        ExprKind::Identifier(name)  => if env.get(name).is_some() { Ok(()) } else { Err(anyhow::anyhow!("Identifier '{}' not declared", name)) },
    }
}

fn analyse_stmt(ast: &Stmt, env: &mut SymbolTable<()>) -> Result<()> {
    match &ast.node {
        crate::ast::StmtKind::FunDecl { name, parameters, return_type, body } => {
            env.push();
            for param in parameters {
                env.insert(param.name.clone(), ());
            }

            analyse_expr(&body, env)?;
            env.pop();
            Ok(())
        },
        crate::ast::StmtKind::StructDecl { name, fields } => todo!(),
        crate::ast::StmtKind::EnumDecl { name, variants } => todo!(),
        crate::ast::StmtKind::TraitDecl { name, methods } => todo!(),
        crate::ast::StmtKind::Top(stmts) => {
            for stmt in stmts {
                analyse_stmt(stmt, env)?;
            }
            Ok(())
        },
    }
}

#[cfg(test)]
mod tests{
    // TODO: ??? ;)
    use super::super::super::parser::parse_ast;

    #[test]
    fn test_semantic_analysis() {
        let ast = parse_ast("fn foo(x: Int): Int = x").unwrap();
        assert!(super::semantic_analysis(&ast).is_ok());

        let ast = parse_ast("fn foo(x: Int): Int = y").unwrap();
        assert!(super::semantic_analysis(&ast).is_err());

        let ast = parse_ast("fn foo(x: Int): Int = x  fn bar(y: Int): Int = x").unwrap();
        assert!(super::semantic_analysis(&ast).is_err());
    }
}
