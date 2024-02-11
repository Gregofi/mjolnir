use crate::ast::Stmt;

extern crate lalrpop_util;
use lalrpop_util::ParseError;
use lalrpop_util::lalrpop_mod;
use lalrpop_util::lexer::Token;

pub fn parse_ast(input: &str) -> Result<Stmt, ParseError<usize, Token<'_>, &'static str>> {
    lalrpop_mod!(pub grammar);
    grammar::TopStmtParser::new().parse(input)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_simple_function() {
        assert!(parse_ast("fn main() = 1").is_ok());
        assert!(parse_ast("fn main(): Int = 1").is_ok());
        assert!(parse_ast("fn foo(a: Int): Int = 1").is_ok());
        assert!(parse_ast("fn foo(a: Int, b: Result): Int = 1").is_ok());
    }

    #[test]
    fn test_multiple_functions() {
        assert!(parse_ast("fn main() = 1\nfn bar() = 2").is_ok());
        assert!(parse_ast("fn main(): Int = 1\nfn baz() = 2 fn bor() = 3").is_ok());
    }
}
