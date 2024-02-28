use crate::ast::Decl;

extern crate lalrpop_util;
use anyhow::{anyhow, Result};
use lalrpop_util::lalrpop_mod;

pub fn parse_ast(input: &str) -> Result<Vec<Decl>> {
    lalrpop_mod!(pub grammar);
    // TODO: This is a quick hack to avoid lifetimes,
    // we should parse the error from parse here and show proper error message.
    grammar::TopLevelDeclsParser::new()
        .parse(input)
        .map_err(|_| anyhow!("Parse error"))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_simple_function() {
        assert!(parse_ast("fn main() = 1").is_ok());
        assert!(parse_ast("fn main() = 1\n").is_ok());
        assert!(parse_ast("fn main(): Int = 1").is_ok());
        assert!(parse_ast("fn foo(a: Int): Int = 1").is_ok());
        assert!(parse_ast("fn foo(a: Int, b: Result): Int = 1").is_ok());
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
}
