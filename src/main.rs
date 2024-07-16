use clap::{Arg, Command};

mod ast;
mod backend;
mod constants;
mod frontend;
mod traits;
mod location;

use backend::ast_interpreter::interpreter::Interpreter;
use frontend::parse_and_check_files;
use location::print_error;

use crate::backend::ast_interpreter::interpreter::NamedModule;

fn main() {
    env_logger::init();
    let matches = Command::new("mjolnir")
        .version("0.1.0")
        .author("Filip Gregor")
        .about("Mjolnir compiler and interpreter")
        .subcommand(
            Command::new("interpret")
                .about("Interpret the given file")
                .arg(Arg::new("file").required(true)),
        )
        .get_matches();
    if let Some(matches) = matches.subcommand_matches("interpret") {
        let file = matches.get_one::<String>("file").unwrap();
        let modules = match parse_and_check_files(file) {
            Ok(m) => m,
            Err(e) => {
                print_error(e);
                std::process::exit(255);
            }
        };
        let mut interpreter = Interpreter::new(
            modules
                .into_iter()
                .map(|(name, module)| (name, NamedModule::from(module)))
                .collect(),
        );
        match interpreter.interpret() {
            Ok(e) => {
                println!("Program exited with code {}", e);
                std::process::exit(e.into());
            }
            Err(e) => {
                println!("Interpreting failed: {}", e);
                std::process::exit(255);
            }
        }
    } else {
        println!("No action specified");
    }
}
