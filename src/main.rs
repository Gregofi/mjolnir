use clap::{Arg, Command};
use frontend::parser::parse_ast;

mod ast;
mod backend;
mod frontend;

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
