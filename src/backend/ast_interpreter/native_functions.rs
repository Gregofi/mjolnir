use super::interpreter::Value;
use crate::frontend;
use crate::frontend::types::{InstantiatedType, Parameter};
use anyhow::Result;
use frontend::types::FunctionType;

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
}

fn _native_ipow(args: Vec<Value>) -> Result<Value> {
    if args.len() != 2 {
        return Err(anyhow::anyhow!("Expected 2 arguments, got {}", args.len()));
    }

    let a = match (&args[0], &args[1]) {
        (Value::Integer(base), Value::Integer(exp)) => {
            let base = *base;
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
                Parameter {
                    name: "base".to_string(),
                    ty: InstantiatedType::get_primitive("Int"),
                },
                Parameter {
                    name: "exp".to_string(),
                    ty: InstantiatedType::get_primitive("Int"),
                },
            ],
            return_type: InstantiatedType::get_primitive("Int"),
        },
    )
}

pub fn get_native_functions() -> Vec<NativeFunction> {
    vec![native_ipow()]
}
