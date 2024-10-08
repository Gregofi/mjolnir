use crate::ast::{Decl, Import};

extern crate lalrpop_util;
use anyhow::{anyhow, Result};
use lalrpop_util::{lalrpop_mod, ParseError};

#[derive(Debug, Clone)]
pub struct ParseErr {
    pub location: usize,
    pub message: String,
}

fn token_readable(token: &str) -> String {
    let s = match token {
        "SEMICOLON" => ";",
        "COLON" => ":",
        "UNDERSCORE" => "_",
        "AMPER" => "&",
        "BANG" => "!",
        "RIGHT_ARROW" => "=>",
        "FAT_RIGHT_ARROW," => "=>",
        "OR," => "||",
        "AND," => "&&",
        "ASSIGN," => "=",
        "EQ," => "==",
        "NEQ," => "!=",
        "GREATER," => ">",
        "LESS," => "<",
        "GREATEREQ," => ">=",
        "LESSEQ," => "<=",
        "MULTIPLY," => "*",
        "DIVIDE," => "/",
        "MODULO," => "%",
        "PLUS," => "+",
        "MINUS," => "-",
        "IF," => "if",
        "ELSE," => "else",
        "LPAREN," => "(",
        "RPAREN," => ")",
        "LET," => "let",
        "LBRACKET," => "[",
        "RBRACKET," => "]",
        "LBRACE," => "{",
        "RBRACE," => "}",
        "PIPE," => "|",
        "TRUE," => "true",
        "FALSE," => "false",
        "FN," => "fn",
        "COMMA," => ",",
        "DOT," => ".",
        "RETURN," => "return",
        "ELIF," => "elif",
        "STRUCT," => "struct",
        "ENUM," => "enum",
        "MATCH," => "match",
        "IMPORT," => "import",
        "FROM," => "from",
        "IMPL," => "impl",
        "DOUBLE_QUOTE," => "\"",
        "SINGLE_QUOTE," => "'",
        _ => token,
    };
    s.to_string()
}

pub fn parse_ast(input: &str) -> Result<(Vec<Import>, Vec<Decl>), ParseErr> {
    lalrpop_mod!(pub grammar);
    // TODO: This is a quick hack to avoid lifetimes,
    // we should parse the error from parse here and show proper error message.
    let result = grammar::ModuleParser::new().parse(input);

    match result {
        Err(e) => match e {
            ParseError::InvalidToken { location } => Err(ParseErr {
                location,
                message: "Invalid token".to_string(),
            }),
            ParseError::UnrecognizedEof { location, expected } => Err(ParseErr {
                location,
                message: format!(
                    "Unrecognized EOF found, expected {:?}",
                    expected
                        .iter()
                        .map(|s| token_readable(&s))
                        .collect::<Vec<String>>()
                ),
            }),
            ParseError::UnrecognizedToken { token, expected } => Err(ParseErr {
                location: token.0,
                message: format!(
                    "Unrecognized token '{}', expected one of {:?}",
                    token.1,
                    expected
                        .iter()
                        .map(|s| token_readable(&s))
                        .collect::<Vec<String>>()
                ),
            }),
            ParseError::ExtraToken { token } => Err(ParseErr {
                location: token.0,
                message: format!("Extra token {}", token.1),
            }),
            ParseError::User { .. } => unimplemented!(),
        },
        Ok(ast) => Ok(ast),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_simple_function() {
        parse_ast("fn main() = true").unwrap();
        assert!(parse_ast("fn main() = 1").is_ok());
        assert!(parse_ast("fn main() = 1\n").is_ok());
        assert!(parse_ast("fn main(): Int = 1").is_ok());
        assert!(parse_ast("fn foo(a: Int): Int = 1").is_ok());
        assert!(parse_ast("fn foo(a: Int, b: Result): Int = 1").is_ok());
        assert!(parse_ast("fn foo(a: Int, b: Result): Unit = ()").is_ok());
    }

    #[test]
    fn test_multiple_functions() {
        assert!(parse_ast("fn main() = 1\nfn bar() = 2").is_ok());
        assert!(parse_ast("fn main(): Int = 1\nfn baz() = 2 fn bor() = 3").is_ok());
    }

    #[test]
    fn test_funcall() {
        assert!(parse_ast("fn main() = foo()").is_ok());
        assert!(parse_ast("fn main() = foo(1, 2)").is_ok());
    }

    #[test]
    fn test_if() {
        assert!(parse_ast("fn main() = if 1 { 2 } else { 3 }").is_ok());
        assert!(parse_ast("fn main() = if 1 { if 2 { 3} else { 4 } } else { 3 }").is_ok());
        assert!(parse_ast("fn main() = if 1 { if 2 { let x = 3; x } else { 4 } } else { 3 }").is_ok());
    }

    #[test]
    fn test_binaries() {
        assert!(parse_ast("fn main() = 1 + 2").is_ok());
        assert!(parse_ast("fn main() = 1 + 2 + 3").is_ok());
        assert!(parse_ast("fn main() = 1 + 2 * 3").is_ok());
        assert!(parse_ast("fn main() = 1 * 2 + 3").is_ok());
        assert!(parse_ast("fn main() = (1 * 2 + 3 == 4) <= 5").is_ok());
    }

    #[test]
    fn test_compound() {
        assert!(parse_ast("fn main(): Int = { 1; 2; 3 }").is_ok());
        assert!(parse_ast("fn main(): Int = { 1; 2; }").is_ok());
        assert!(parse_ast("fn main(): Int = { }").is_ok());
        assert!(parse_ast("fn main(): Int = { 1; }").is_ok());
        assert!(parse_ast("fn main(): Int = { 1 }").is_ok());
        assert!(parse_ast("fn main(): Int = { foo(); }").is_ok());
    }

    #[test]
    fn test_var_decls() {
        assert!(parse_ast("fn main() = { let a: Int = 1; a }").is_ok());
    }

    #[test]
    fn test_enums() {
        //        assert!(parse_ast(
        //            "
        //enum Foo {
        //    A{}, B{}, C{}
        //}
        //"
        //        )
        //        .is_ok());
        //        assert!(parse_ast(
        //            "
        //enum Foo {
        //    A{}
        //}
        //"
        //        )
        //        .is_ok());
        //        assert!(parse_ast(
        //            "
        //enum Foo {
        //    A{a: Int},
        //}
        //"
        //        )
        //        .is_ok());
        //        assert!(parse_ast(
        //            "
        //enum List {
        //    Cons{head: Int, tail: List},
        //    Nil{}
        //}
        //"
        //        )
        //        .is_ok());

        assert!(parse_ast(
            "
enum List {
    Cons(Int, List),
    Nil,
}
"
        )
        .is_ok());
    }

    #[test]
    fn test_structs() {
        assert!(parse_ast(
            "
struct Foo {
    a: Int,
    b: Int,
}
"
        )
        .is_ok());

        assert!(parse_ast(
            "
struct Foo {
    a: Int,
    b: Int,
}

fn foo(): Foo = &Foo{a: 1, b: 2}
"
        )
        .is_ok());

        assert!(parse_ast(
            "
struct Foo {
    a: Int,
    b: Int,
}

fn foo(): Foo = &Foo{a: &Bar{a: Null, b: 4}, b: 2}
"
        )
        .is_ok());
    }

    #[test]
    fn test_match() {
        assert!(parse_ast(
            "
fn main() = match 1 {
    1 => 2,
    2 => 3,
    _ => 4,
}
"
        )
        .is_ok());

        assert!(parse_ast(
            "
fn main() = match a {
    Foo{name, age} => 2,
    Bar{name, age} => 3,
}
"
        )
        .is_ok());

        assert!(parse_ast(
            "
fn main() = match a {
    Cons(head, tail) => 2,
    Nil() => 3,
}
"
        )
        .is_ok());
    }

    #[test]
    fn test_generics() {
        assert!(parse_ast(
            "
enum List[T] {
    Cons(T, List[T]),
    Nil,
}

fn main() = match Cons(1, a) {
    Cons(head, tail) => 2,
    Nil() => 3,
}
"
        )
        .is_ok());
    }

    #[test]
    fn test_function_types() {
        assert!(parse_ast(
            "
fn main(f: (Int) => Int) = f(1)
"
        )
        .is_ok());
        assert!(parse_ast(
            "
fn main(f: (Int, List[T]) => List[T]) = f(1)
"
        )
        .is_ok());
        assert!(parse_ast(
            "
fn main(f: (Int) => (Int) => (Int) => Int) = f(1)
"
        )
        .is_ok());
    }

    #[test]
    fn test_chars() {
        assert!(parse_ast(
            "
fn bar() = 'a'
fn foo() = '\n'
fn foy() = '\0'
fn baz() = if x == 'a' { 1 } else { 0 }
"
        )
        .is_ok());
    }

    #[test]
    fn test_imports() {
        let (imports, _) = parse_ast(
            "
import { foo } from \"foo\";
import { bar, baz } from \"./baz\";

fn main() = foo()
",
        )
        .unwrap();
        assert_eq!(imports.len(), 2);
        assert_eq!(imports[0].imported_ids, vec!["foo"]);
        assert_eq!(imports[0].path, "foo");
        assert_eq!(imports[1].imported_ids, vec!["bar", "baz"]);
        assert_eq!(imports[1].path, "./baz");
    }

    #[test]
    fn test_lambdas() {
        assert!(parse_ast("fn foo() = |a: Int| { a + 1 }").is_ok());
        assert!(parse_ast("fn foo(lst) = lst.map(|x| { x * 2 })").is_ok());
    }

    #[test]
    fn test_comments() {
        assert!(parse_ast(
            "// This is a comment
// This is another comment
fn foo() = 1

/// Doc comment
fn bar() = {
    // comment inside ;)
    2
    /* Multiline comment
    */
}
"
        )
        .is_ok());
    }
}
