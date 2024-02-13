use clap::{Arg, Command};
use parser::parse_ast;

mod ast;
mod frontend;
mod parser;

fn main() {
    let matches = Command::new("My Super Program")
        .version("1.0")
        .author("Filip Gregor")
        .about("Mjolnir compiler")
        .arg(Arg::new("file").required(true).index(1))
        .get_matches();
    let f: String = matches.get_one::<String>("file").unwrap().to_string();
    parse_ast(&f).unwrap();
}
