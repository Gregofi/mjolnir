use crate::ast::TypedDecl;
use anyhow::anyhow;
use anyhow::Result;

pub mod parser;
// pub mod semantic_analysis;
mod type_ast;
pub mod type_inference;
pub mod types;
pub mod utils;

#[allow(dead_code)]
pub fn do_frontend_pass(program: &str) -> Result<Vec<TypedDecl>> {
    let ast = parser::parse_ast(program)?;
    let inferred =
        type_inference::type_inference(ast).map_err(|e| anyhow!("Type inference failed: {}", e))?;
    // Will be used later.
    // let types = type_ast::collect_decls(&inferred);
    let typed = type_ast::type_ast(inferred);
    typed.map_err(|e| anyhow!("AST Typing failed: {}", e))
}
