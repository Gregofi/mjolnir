use anyhow::{anyhow, Context, Result};
use std::{collections::HashMap, rc::Rc};

use crate::ast::{
    ExprKind, Operator, TypedDecl, TypedDeclKind, TypedExpr, TypedStmt, TypedStmtKind,
};

const MAIN_FUNCTION_NAME: &str = "main";

#[derive(Clone)]
enum Value {
    Integer(i64),
    Float(f64),
    String(Rc<String>),
    Bool(bool),
    Unit,
    Function { body: TypedExpr },
}

struct CallEnvironment {
    env: Vec<HashMap<String, Value>>,
}

impl CallEnvironment {
    pub fn add_identifier(&mut self, name: String, value: Value) {
        self.env
            .last_mut()
            .expect("No environment, use push first!")
            .insert(name, value);
    }

    pub fn get_identifier(&self, name: &String) -> Option<&Value> {
        self.env.iter().rev().find_map(|env| env.get(name))
    }

    pub fn push(&mut self) {
        self.env.push(HashMap::new());
    }

    pub fn pop(&mut self) {
        self.env.pop();
    }
}

struct CallStack {
    stack: Vec<CallEnvironment>,
}

impl CallStack {
    pub fn new() -> CallStack {
        CallStack { stack: vec![] }
    }

    /// Pushes a new call environment to the stack with one layer.
    pub fn push_call(&mut self) {
        self.stack.push(CallEnvironment {
            env: vec![HashMap::new()],
        });
    }

    pub fn pop_call(&mut self) {
        self.stack.pop();
    }

    pub fn add_identifier(&mut self, name: String, value: Value) {
        self.stack
            .last_mut()
            .expect("No environment, use push first!")
            .add_identifier(name, value);
    }

    pub fn get_identifier(&self, name: &String) -> Option<&Value> {
        self.stack
            .last()
            .expect("No environment, use push first!")
            .get_identifier(name)
    }

    pub fn get_env(&mut self) -> &mut CallEnvironment {
        self.stack
            .last_mut()
            .expect("No environment, use push first!")
    }
}

struct Interpreter {
    call_stack: CallStack,
    globals: HashMap<String, Value>,
}

impl Interpreter {
    pub fn new(top_decls: HashMap<String, TypedDecl>) -> Self {
        let mut globals = HashMap::new();
        for (name, decl) in top_decls.iter() {
            let value_decl = match &decl.node {
                TypedDeclKind::FunDecl { body, .. } => Some(Value::Function {
                    body: *body.clone(),
                }),
                _ => None,
            };

            if let Some(value) = value_decl {
                globals.insert(name.clone(), value);
            }
        }
        Interpreter {
            call_stack: CallStack::new(),
            globals,
        }
    }

    pub fn interpret_expr(&mut self, expr: &TypedExpr) -> Result<Value> {
        match &expr.node {
            ExprKind::Int(int) => Ok(Value::Integer(*int)),
            ExprKind::Boolean(bool) => Ok(Value::Bool(*bool)),
            ExprKind::Identifier(id) => {
                let mut value = self.call_stack.get_identifier(id);
                if value.is_none() {
                    value = self.globals.get(id);
                }
                match value {
                    None => Err(anyhow!("Identifier not found: {}", id)),
                    Some(value) => Ok(value.clone()),
                }
            }
            ExprKind::Compound(stmts, expr) => {
                todo!()
            }
            ExprKind::FunCall { target, args } => {
                // Evaluate arguments with current environment
                let args_values = args
                    .iter()
                    .map(|arg| self.interpret_expr(arg))
                    .collect::<Result<Vec<Value>>>()?;

                self.call_stack.push_call();
                let fun_type = target.ty.as_function().expect(
                    "Function call must have function type; Should be caught by semantic analysis",
                );
                for (param, arg) in fun_type.parameters.iter().zip(args_values.iter()) {
                    self.call_stack
                        .add_identifier(param.name.clone(), arg.clone());
                }

                let resulting_function = self.interpret_expr(target)?;
                match resulting_function {
                    Value::Function { body } => {
                        let result = self.interpret_expr(&body)?;
                        self.call_stack.pop_call();
                        Ok(result)
                    },
                    _ => Err(anyhow!("Target of function call must be a function; Should be caught by semantic analysis")),
                }
            }
            ExprKind::If { cond, then, els } => {
                let cond_val = self.interpret_expr(cond)?;
                match cond_val {
                    Value::Bool(true) => self.interpret_expr(then),
                    Value::Bool(false) => self.interpret_expr(els),
                    _ => Err(anyhow!("If condition must be boolean")),
                }
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let lhs_val = self.interpret_expr(lhs)?;
                let rhs_val = self.interpret_expr(rhs)?;
                match (lhs_val, rhs_val) {
                    (Value::Integer(lhs), Value::Integer(rhs)) => {
                        let res = match op {
                            Operator::Add => Value::Integer(lhs + rhs),
                            Operator::Sub => Value::Integer(lhs - rhs),
                            Operator::Mul => Value::Integer(lhs * rhs),
                            Operator::Div => Value::Integer(lhs / rhs),
                            Operator::Mod => Value::Integer(lhs % rhs),
                            Operator::Equal => Value::Bool(lhs == rhs),
                            Operator::Neq => Value::Bool(lhs != rhs),
                            Operator::Less => Value::Bool(lhs < rhs),
                            Operator::Greater => Value::Bool(lhs > rhs),
                            Operator::LessEqual => Value::Bool(lhs <= rhs),
                            Operator::GreaterEqual => Value::Bool(lhs >= rhs),
                            _ => todo!(),
                        };
                        Ok(res)
                    }
                    _ => panic!(
                        "Invalid types for binary operator, should be catched by semantic analysis"
                    ),
                }
            }
        }
    }

    /**
     * Receives top level declarations and interprets them.
     */
    pub fn interpret(&mut self) -> Result<u8> {
        let main = self
            .globals
            .get(MAIN_FUNCTION_NAME)
            .context("No main function found")?;
        let main_body = match main {
            Value::Function { body } => {
                body.clone() // FIXME: borrow checker is not happy
            }
            _ => return Err(anyhow!("Main function must be a function")),
        };

        self.call_stack.push_call();
        let val = self.interpret_expr(&main_body)?;
        match val {
            Value::Integer(x) if x > 0 && x < 256 => Ok(x.try_into().unwrap()),
            Value::Integer(_) => Err(anyhow!(
                "Main function must return unit or integer between 0 and 255"
            )),
            Value::Unit => Ok(0),
            _ => Err(anyhow!("Main function must return integer or unit")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::parse_ast;

    #[test]
    fn test_interpret_main() {
        let ast = parse_ast("fn main(): Int = 5").unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 5);

        let ast = parse_ast("fn main(): Int = 1 + 2").unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 3);
    }

    #[test]
    fn test_interpreter_if() {
        let ast = parse_ast("fn main(): Int = if true { 1 } else { 2 }").unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 1);

        let ast = parse_ast("fn main(): Int = if false { 1 } else { 2 }").unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 2);
    }

    #[test]
    fn test_fun_call() {
        let ast = parse_ast(
            "
fn fact(n: Int): Int = if n == 0 { 1 } else { n * fact(n - 1) }

fn main(): Int = fact(5)
",
        );
        let mut interpreter = Interpreter::new(ast.unwrap());
        assert_eq!(interpreter.interpret().unwrap(), 120);
    }
}
