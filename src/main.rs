use lalrpop_util::lalrpop_mod;

extern crate lalrpop_util;

lalrpop_mod!(pub grammar);

mod ast;
mod parser;

fn main() {
    println!("Hello, world!");
}
