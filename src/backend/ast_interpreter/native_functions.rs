use super::ast_interpreter::Value;
use crate::frontend;
use anyhow::Result;
use frontend::types::{FunctionType, Type};
use frontend::utils::TypedIdentifier;
use lazy_static::lazy_static;

#[derive(Clone)]
pub struct NativeFunction {
    pub name: String,
    pub body: fn(Vec<Value>) -> Result<Value>,
    pub ty: FunctionType,
}

impl NativeFunction {
    pub fn new(name: String, body: fn(Vec<Value>) -> Result<Value>, ty: FunctionType) -> Self {
        Self { name, body, ty }
    }

    pub fn call(&self, args: Vec<Value>) -> Result<Value> {
        (self.body)(args)
    }
}

fn _native_iprintln(args: Vec<Value>) -> Result<Value> {
    if let [Value::Integer(i)] = args.as_slice() {
        println!("{}", i);
    } else {
        return Err(anyhow::anyhow!("Expected integer"));
    }
    Ok(Value::Unit)
}

fn native_iprintln() -> NativeFunction {
    NativeFunction::new(
        "iprintln".to_string(),
        _native_iprintln,
        FunctionType {
            parameters: vec![TypedIdentifier {
                name: "_".to_string(),
                ty: Type::get_int(),
            }],
            return_type: Type::get_unit(),
        },
    )
}

fn _native_ipow(args: Vec<Value>) -> Result<Value> {
    if args.len() != 2 {
        return Err(anyhow::anyhow!("Expected 2 arguments, got {}", args.len()));
    }

    let a = match (&args[0], &args[1]) {
        (Value::Integer(base), Value::Integer(exp)) => {
            let base = *base as i64;
            if *exp < 0 {
                Err(anyhow::anyhow!("Exponent must be non-negative"))
            } else {
                let exp = *exp as u32;
                Ok(base.pow(exp))
            }
        }
        _ => Err(anyhow::anyhow!("Expected integer")),
    }?;

    Ok(Value::Integer(a as i64))
}

fn native_ipow() -> NativeFunction {
    NativeFunction::new(
        "ipow".to_string(),
        _native_ipow,
        FunctionType {
            parameters: vec![
                TypedIdentifier {
                    name: "base".to_string(),
                    ty: Type::get_int(),
                },
                TypedIdentifier {
                    name: "exp".to_string(),
                    ty: Type::get_int(),
                },
            ],
            return_type: Type::get_int(),
        },
    )
}

pub fn get_native_functions() -> Vec<NativeFunction> {
    vec![native_iprintln(), native_ipow()]
}
