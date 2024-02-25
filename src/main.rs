use clap::{Arg, Command};
use frontend::parser::parse_ast;

mod ast;
mod backend;
mod frontend;

use backend::ast_interpreter::ast_interpreter::Interpreter;
use frontend::semantic_analysis::semantic_analysis;

fn main() {
    let matches = Command::new("My Super Program")
        .version("1.0")
        .author("Filip Gregor")
        .about("Mjolnir compiler")
        .arg(Arg::new("file").required(true).index(1))
        .get_matches();
    let f: String = matches.get_one::<String>("file").unwrap().to_string();
    let file_contents = std::fs::read_to_string(&f).unwrap();
    let ast = parse_ast(&file_contents).unwrap();
    let typed_ast = semantic_analysis(&ast).unwrap();
    let mut interpreter = Interpreter::new(typed_ast);
    let exit_code = interpreter.interpret().unwrap();
    println!("Process exited with exit code {}", exit_code);
}
