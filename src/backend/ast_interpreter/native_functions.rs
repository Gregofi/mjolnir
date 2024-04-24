use std::rc::Rc;

use super::interpreter::Value;
use crate::frontend;
use crate::frontend::type_inference::{Constructor, Type};
use anyhow::Result;
use frontend::type_inference::TypeScheme;

#[derive(Clone)]
pub struct NativeFunction {
    pub name: String,
    pub body: fn(Vec<Value>) -> Result<Value>,
    pub ty: TypeScheme,
}

impl NativeFunction {
    pub fn new(name: String, body: fn(Vec<Value>) -> Result<Value>, ty: TypeScheme) -> Self {
        Self { name, body, ty }
    }
}

fn vec_to_list(v: Vec<Value>) -> Value {
    let mut list = Value::Variant {
        name: "Nil".to_string(),
        fields: Rc::new(vec![]),
    };
    for i in (0..v.len()).rev() {
        list = Value::Variant {
            name: "Cons".to_string(),
            fields: Rc::new(vec![v[i].clone(), list]),
        };
    }
    list
}

impl Type {
    pub fn create_list(of: String) -> Rc<Type> {
        Rc::new(Type::Constructor(Constructor {
            name: "List".to_string(),
            type_vec: vec![Type::create_constant(of)],
        }))
    }
}

fn _native_assert(args: Vec<Value>) -> Result<Value> {
    if args.len() != 1 {
        return Err(anyhow::anyhow!("Expected 1 argument, got {}", args.len()));
    }

    match &args[0] {
        Value::Bool(b) => {
            if !(*b) {
                return Err(anyhow::anyhow!("Assertion failed"));
            }
        }
        _ => return Err(anyhow::anyhow!("Expected boolean")),
    };
    Ok(Value::Unit)
}

fn native_putchar() -> NativeFunction {
    NativeFunction::new(
        "putchar".to_string(),
        |args| {
            if args.len() != 1 {
                return Err(anyhow::anyhow!("Expected 1 argument, got {}", args.len()));
            }

            match &args[0] {
                Value::Char(c) => {
                    print!("{}", c);
                    Ok(Value::Unit)
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

/// needs: stdlib List
fn native_readln() -> NativeFunction {
    NativeFunction::new(
        "readln".to_string(),
        |args| {
            if !args.is_empty() {
                return Err(anyhow::anyhow!("Expected 0 arguments, got {}", args.len()));
            }

            let mut input = String::new();
            std::io::stdin().read_line(&mut input)?;
            Ok(vec_to_list(
                input
                    .trim_end_matches('\n')
                    .chars()
                    .map(|c| Value::Char(c))
                    .collect(),
            ))
        },
        TypeScheme {
            generics: vec![],
            ty: Type::create_function(vec![], Type::create_list("Char".to_string())).into_rc(),
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

            match (&args[0], &args[1]) {
                (Value::Integer(a), Value::Integer(b)) => Ok(Value::Integer(a.pow(*b as u32))),
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
        native_readln(),
    ]
}
