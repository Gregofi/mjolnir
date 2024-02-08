#[cfg(test)]
mod test {
    use lalrpop_util::lalrpop_mod;
    lalrpop_mod!(pub grammar);

    #[test]
    fn test_parser() {
        assert!(grammar::TopStmtParser::new().parse("fn main() = 1").is_ok());
        assert!(grammar::TopStmtParser::new().parse("fn main(): Int = 1").is_ok());
        assert!(grammar::TopStmtParser::new().parse("fn foo(a: Int): Int = 1").is_ok());
        assert!(grammar::TopStmtParser::new().parse("fn foo(a: Int, b: Result): Int = 1").is_ok());
    }
}
