use clap::{Arg, Command};
use frontend::parser::parse_ast;

mod ast;
mod backend;
mod frontend;
mod traits;

use backend::ast_interpreter::interpreter::Interpreter;
use frontend::do_frontend_pass;
use frontend::type_inference::type_inference;

use backend::ast_interpreter::interpreter::decls_to_hashmap;

fn main() {
    env_logger::init();
    let matches = Command::new("mjolnir")
        .version("1.0")
        .author("Filip Gregor")
        .about("Mjolnir compiler and interpreter")
        .subcommand(
            Command::new("type-inference")
                .about("Invoke the type inference algorithm and print the result")
                .arg(Arg::new("file").required(true)),
        )
        .subcommand(
            Command::new("interpret")
                .about("Interpret the given file")
                .arg(Arg::new("file").required(true)),
        )
        .get_matches();
    if let Some(matches) = matches.subcommand_matches("type-inference") {
        let file = matches.get_one::<String>("file").unwrap();
        let contents = std::fs::read_to_string(file).expect("Error reading file");
        let ast = parse_ast(&contents).unwrap();
        let ast = type_inference(ast).expect("Type inference failed");
        for decl in ast {
            println!("{}", decl.display_pretty());
        }
    } else if let Some(matches) = matches.subcommand_matches("interpret") {
        let file = matches.get_one::<String>("file").unwrap();
        let contents = std::fs::read_to_string(file).expect("Error reading file");
        let ast = do_frontend_pass(&contents).unwrap();

        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        match interpreter.interpret() {
            Ok(e) => {
                println!("Program exited with code {}", e);
            }
            Err(e) => {
                println!("Interpreting failed: {}", e);
            }
        }
    } else {
        println!("No action specified");
    }
}
