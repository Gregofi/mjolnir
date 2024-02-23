use std::collections::HashMap;

use anyhow::Result;
use crate::ast::TypedDecl;

pub mod semantic_analysis;
pub mod types;
pub mod parser;
mod utils;

pub fn parse_ast<'a>(program: &str) -> Result<HashMap<String, TypedDecl>> {
    let ast = parser::parse_ast(program)?;
    let typed = semantic_analysis::semantic_analysis(&ast)?;
    Ok(typed)
}
