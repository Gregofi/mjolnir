use std::{collections::HashMap, rc::Rc};
use anyhow::{Result, Context, anyhow};

use crate::ast::{TypedDecl, TypedDeclKind, TypedExpr, ExprKind, TypedStmtKind, TypedStmt, Operator};

const MAIN_FUNCTION_NAME: &str = "main";

#[derive(Clone)]
enum Value {
    Integer(i64),
    Float(f64),
    String(Rc<String>),
    Bool(bool),
    Unit,
    Function,
}

struct Env {
    identifiers: HashMap<String, Value>,
}

impl Env {
    pub fn add_identifier(&mut self, name: String, value: Value) {
        self.identifiers.insert(name, value);
    }

    pub fn get_identifier(&self, name: &String) -> Option<&Value> {
        self.identifiers.get(name)
    }
}

struct Interpreter {
    env: Vec<Env>,
    top_decls: HashMap<String, TypedDecl>,
}

impl Interpreter {
    pub fn new(top_decls: HashMap<String, TypedDecl>) -> Interpreter {
        Interpreter { env: vec![], top_decls }
    }

    pub fn push_env(&mut self) {
        self.env.push(Env { identifiers: HashMap::new() });
    }

    pub fn pop_env(&mut self) {
        self.env.pop();
    }

    pub fn add_identifier(&mut self, name: String, value: Value) {
        self.env.last_mut().expect("No environment, use push_env first!").add_identifier(name, value);
    }

    pub fn get_identifier(&self, name: &String) -> Option<&Value> {
        for env in self.env.iter().rev() {
            if let Some(value) = env.get_identifier(name) {
                return Some(value);
            }
        }
        None
    }

    pub fn interpret_expr(&mut self, expr: &TypedExpr) -> Result<Value> {
        match &expr.node {
            ExprKind::Int(int) => Ok(Value::Integer(*int)),
            ExprKind::Boolean(bool) => Ok(Value::Bool(*bool)),
            ExprKind::Identifier(id) => {
                let value = self.get_identifier(id).with_context(|| format!("Identifier {} not found", id))?.clone();
                Ok(value)
            }
            ExprKind::Compound(stmts, expr) => todo!(),
            ExprKind::FunCall { target, args } => {
                todo!()
            },
            ExprKind::If { cond, then, els } => {
                let cond_val = self.interpret_expr(cond)?;
                match cond_val {
                    Value::Bool(true) => self.interpret_expr(then),
                    Value::Bool(false) => self.interpret_expr(els),
                    _ => Err(anyhow!("If condition must be boolean")),
                }
            },
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
                    _ => panic!("Invalid types for binary operator, should be catched by semantic analysis"),
                }
            },
        }
    }

    /**
     * Receives top level declarations and interprets them.
     */
    pub fn interpret(&mut self) -> Result<u8> {
        self.push_env();
        let main = self.top_decls.get(MAIN_FUNCTION_NAME).context("No main function found")?;
        let main_body = match &main.node {
            TypedDeclKind::FunDecl{name, body, ..} => {
                assert!(name == MAIN_FUNCTION_NAME);
                body.clone() // FIXME: borrow checker is not happy
            },
            TypedDeclKind::VarDecl(_) => {
                return Err(anyhow!("Main must be a function, not variable declaration"))
            },
        };

        let val = self.interpret_expr(&main_body)?;
        match val {
            Value::Integer(x) if x > 0 && x < 256 => Ok(x.try_into().unwrap()),
            Value::Integer(_) => Err(anyhow!("Main function must return unit or integer between 0 and 255")),
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
}
