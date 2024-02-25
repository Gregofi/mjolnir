use std::collections::HashMap;

use crate::ast::TypedDecl;
use anyhow::Result;

pub mod parser;
pub mod semantic_analysis;
pub mod types;
pub mod utils;

#[allow(dead_code)]
pub fn parse_ast<'a>(program: &str) -> Result<HashMap<String, TypedDecl>> {
    let ast = parser::parse_ast(program)?;
    let typed = semantic_analysis::semantic_analysis(&ast)?;
    Ok(typed)
}
