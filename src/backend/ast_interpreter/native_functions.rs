use std::io::Read;
use std::rc::Rc;

use super::interpreter::Value;
use crate::frontend;
use crate::frontend::type_inference::{Constructor, Type};
use anyhow::Result;
use frontend::type_inference::TypeScheme;

#[derive(Clone, Debug)]
pub struct NativeFunction {
    pub name: String,
    pub body: fn(Vec<Rc<Value>>) -> Result<Rc<Value>>,
    pub ty: TypeScheme,
}

impl NativeFunction {
    pub fn new(name: String, body: fn(Vec<Rc<Value>>) -> Result<Rc<Value>>, ty: TypeScheme) -> Self {
        Self { name, body, ty }
    }
}

impl Type {
    pub fn create_list(of: String) -> Rc<Type> {
        Rc::new(Type::Constructor(Constructor {
            name: "List".to_string(),
            type_vec: vec![Type::create_constant(of)],
        }))
    }
}

fn _native_assert(args: Vec<Rc<Value>>) -> Result<Rc<Value>> {
    if args.len() != 1 {
        return Err(anyhow::anyhow!("Expected 1 argument, got {}", args.len()));
    }

    match &*args[0] {
        Value::Bool(b) => {
            if !(*b) {
                return Err(anyhow::anyhow!("Assertion failed"));
            }
        }
        _ => return Err(anyhow::anyhow!("Expected boolean")),
    };
    Ok(Value::Unit.into())
}

fn native_putchar() -> NativeFunction {
    NativeFunction::new(
        "putchar".to_string(),
        |args| {
            if args.len() != 1 {
                return Err(anyhow::anyhow!("Expected 1 argument, got {}", args.len()));
            }

            match &*args[0] {
                Value::Char(c) => {
                    print!("{}", *c as char);
                    Ok(Value::Unit.into())
                }
                _ => Err(anyhow::anyhow!("Expected char")),
            }
        },
        TypeScheme {
            generics: vec![],
            ty: Type::create_function(
                vec![Type::create_constant("Char".to_string())],
                Type::create_constant("Unit".to_string()),
            )
            .into_rc(),
        },
    )
}

fn native_getchar() -> NativeFunction {
    NativeFunction::new(
        "getchar".to_string(),
        |_args| {
            let x = std::io::stdin().bytes().next();
            if x.is_none() {
                // eof
                Ok(Value::Char(0).into())
            } else {
                let x = x.unwrap();
                match x {
                    Ok(c) => Ok(Value::Char(c).into()),
                    Err(e) => Err(anyhow::anyhow!("Error reading char: {}", e)),
                }
            }
        },
        TypeScheme {
            generics: vec![],
            ty: Type::create_function(vec![], Type::create_constant("Char".to_string())).into_rc(),
        },
    )
}

fn native_assert() -> NativeFunction {
    NativeFunction::new(
        "assert".to_string(),
        _native_assert,
        TypeScheme {
            generics: vec![],
            ty: Type::create_function(
                vec![Type::create_constant("Bool".to_string())],
                Type::create_constant("Unit".to_string()),
            )
            .into_rc(),
        },
    )
}

fn native_pow() -> NativeFunction {
    NativeFunction::new(
        "pow".to_string(),
        |args| {
            if args.len() != 2 {
                return Err(anyhow::anyhow!("Expected 2 arguments, got {}", args.len()));
            }

            match (&*args[0], &*args[1]) {
                (Value::Integer(a), Value::Integer(b)) => Ok(Value::Integer(a.pow(*b as u32)).into()),
                _ => Err(anyhow::anyhow!("Expected two integers")),
            }
        },
        TypeScheme {
            generics: vec![],
            ty: Type::create_function(
                vec![
                    Type::create_constant("Int".to_string()),
                    Type::create_constant("Int".to_string()),
                ],
                Type::create_constant("Int".to_string()),
            )
            .into_rc(),
        },
    )
}

pub fn get_native_functions() -> Vec<NativeFunction> {
    vec![
        native_assert(),
        native_pow(),
        native_putchar(),
        native_getchar(),
    ]
}
