use anyhow::{anyhow, Context, Result};
use std::fmt::{self, Display, Formatter};
use std::{collections::HashMap, rc::Rc};

use crate::ast::{
    ExprKind, Operator, Pattern, TypedDecl, TypedDeclKind, TypedExpr, TypedStmt, TypedStmtKind,
};

use super::native_functions;
use super::native_functions::NativeFunction;

const MAIN_FUNCTION_NAME: &str = "main";

#[derive(Clone)]
pub struct StructValue {
    name: String,
    fields: HashMap<String, Value>,
}

#[derive(Clone)]
pub enum Value {
    Integer(i64),
    Bool(bool),
    Char(char),
    Unit,
    Function {
        body: TypedExpr,
        parameters: Vec<String>,
    },
    NativeFunction(native_functions::NativeFunction),
    Constructor {
        name: String,
        param_cnt: usize,
    },
    Struct(StructValue),
    Variant {
        name: String,
        fields: Rc<Vec<Value>>,
    },
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Value::Integer(i) => write!(f, "{}", i),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Char(c) => write!(f, "{}", c),
            Value::Unit => write!(f, "()"),
            Value::Function { .. } => write!(f, "Function"),
            Value::NativeFunction(_) => write!(f, "NativeFunction"),
            Value::Struct(StructValue { name, fields }) => {
                write!(f, "{} {{", name)?;
                for (field, value) in fields.iter() {
                    write!(f, "{}: {}, ", field, value)?;
                }
                write!(f, "}}")
            }
            Value::Variant { name, fields } => {
                write!(f, "{}(", name)?;
                for field in fields.iter() {
                    write!(f, "{}, ", field)?;
                }
                write!(f, ")")
            }
            Value::Constructor { name, .. } => write!(f, "Constructor({})", name),
        }
    }
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

pub struct Interpreter {
    call_stack: CallStack,
    globals: HashMap<String, Value>,
}

impl Interpreter {
    pub fn new(top_decls: HashMap<String, TypedDecl>) -> Self {
        let mut globals = HashMap::new();
        for (name, decl) in top_decls.iter() {
            let value_decl = match &decl.node {
                TypedDeclKind::FunDecl {
                    body, parameters, ..
                } => Some(Value::Function {
                    body: *body.clone(),
                    parameters: parameters.iter().map(|p| p.name.clone()).collect(),
                }),
                TypedDeclKind::EnumDecl { variants, .. } => {
                    for variant in variants {
                        let param_cnt = variant.fields.len();
                        let name = variant.name.clone();
                        let cons = Value::Constructor {
                            name: name.clone(),
                            param_cnt,
                        };
                        globals.insert(name, cons);
                    }
                    None
                }
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

    pub fn try_match(pattern: &Pattern, match_target: &Value) -> Option<HashMap<String, Value>> {
        match (pattern, match_target) {
            (Pattern::Wildcard, _) => Some(HashMap::new()),
            (Pattern::Int(pval), Value::Integer(vval)) if pval == vval => Some(HashMap::new()),
            (Pattern::Boolean(pval), Value::Bool(vval)) if pval == vval => Some(HashMap::new()),
            (
                Pattern::Struct {
                    name: pname,
                    fields: pfields,
                },
                Value::Struct(StructValue {
                    name: vname,
                    fields: vfields,
                }),
            ) if pname == vname => {
                let mut ids = HashMap::new();
                for field in pfields {
                    let value = vfields.get(field).expect("Field not found").clone();
                    ids.insert(field.clone(), value.clone());
                }
                Some(ids)
            }
            (
                Pattern::Enum {
                    name: enum_name,
                    patterns,
                },
                Value::Variant {
                    name: variant_name,
                    fields,
                },
            ) if enum_name == variant_name => {
                let mut map = HashMap::new();
                for (pattern, value) in patterns.iter().zip(fields.iter()) {
                    let ids = Interpreter::try_match(pattern, value);
                    if let Some(ids) = ids {
                        for (id, value) in ids {
                            map.insert(id, value);
                        }
                    } else {
                        return None;
                    }
                }
                Some(map)
            }
            (Pattern::Identifier(id), _) => {
                let mut map = HashMap::new();
                map.insert(id.clone(), match_target.clone());
                Some(map)
            }
            _ => None,
        }
    }

    pub fn interpret_expr(&mut self, expr: &TypedExpr) -> Result<Value> {
        match &expr.node {
            ExprKind::Unit => Ok(Value::Unit),
            ExprKind::Int(int) => Ok(Value::Integer(*int)),
            ExprKind::Boolean(bool) => Ok(Value::Bool(*bool)),
            ExprKind::Char(c) => Ok(Value::Char(*c)),
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
                self.call_stack.get_env().push();
                for stmt in stmts {
                    self.interpret_stmt(stmt)?;
                }
                let ret = self.interpret_expr(expr);
                self.call_stack.get_env().pop();
                ret
            }
            ExprKind::FunCall { target, args } => {
                // Evaluate arguments with current environment
                let args_values = args
                    .iter()
                    .map(|arg| self.interpret_expr(arg))
                    .collect::<Result<Vec<Value>>>()?;

                self.call_stack.push_call();

                let resulting_function = self.interpret_expr(target)?;
                match resulting_function {
                    Value::Function { body, parameters } => {
                        for (param, arg) in parameters.iter().zip(args_values.iter()) {
                            self.call_stack.add_identifier(param.clone(), arg.clone());
                        }
                        let result = self.interpret_expr(&body)?;
                        self.call_stack.pop_call();
                        Ok(result)
                    },
                    Value::NativeFunction(NativeFunction{body, ..}) => {
                        let result = body(args_values)?;
                        self.call_stack.pop_call();
                        Ok(result)
                    },
                    Value::Constructor{name, param_cnt: _} => {
                        let result = Value::Variant {
                            name,
                            fields: Rc::new(args_values),
                        };
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
                    (Value::Bool(lhs), Value::Bool(rhs)) => {
                        let res = match op {
                            Operator::Equal => Value::Bool(lhs == rhs),
                            Operator::Neq => Value::Bool(lhs != rhs),
                            _ => panic!("Invalid operator for boolean values"),
                        };
                        Ok(res)
                    }
                    (Value::Char(lhs), Value::Char(rhs)) => {
                        let res = match op {
                            Operator::Equal => Value::Bool(lhs == rhs),
                            Operator::Neq => Value::Bool(lhs != rhs),
                            Operator::Less => Value::Bool(lhs < rhs),
                            Operator::Greater => Value::Bool(lhs > rhs),
                            Operator::LessEqual => Value::Bool(lhs <= rhs),
                            Operator::GreaterEqual => Value::Bool(lhs >= rhs),
                            Operator::Sub => Value::Integer(lhs as i64 - rhs as i64),
                            _ => panic!("Invalid operator for char values"),
                        };
                        Ok(res)
                    }
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
                        };
                        Ok(res)
                    }
                    _ => panic!(
                        "Invalid types for binary operator, should be catched by semantic analysis"
                    ),
                }
            }
            ExprKind::Match { target, arms } => {
                let target = self.interpret_expr(target)?;
                for arm in arms {
                    let ids = Interpreter::try_match(&arm.pattern, &target);
                    if let Some(ids) = ids {
                        self.call_stack.get_env().push();
                        for (id, value) in ids {
                            self.call_stack.add_identifier(id, value);
                        }

                        if let Some(cond) = arm.cond.as_ref() {
                            let cond_val = self.interpret_expr(cond)?;
                            if let Value::Bool(x) = cond_val {
                                if !x {
                                    self.call_stack.get_env().pop();
                                    continue;
                                }
                            } else {
                                return Err(anyhow!("Condition in match must be boolean"));
                            }
                        }

                        let result = self.interpret_expr(&arm.body);

                        self.call_stack.get_env().pop();
                        return result;
                    }
                }
                Err(anyhow!(
                    "No match found; Should be caught by semantic analysis"
                ))
            }
            ExprKind::StructInitializer { name, fields, .. } => {
                let vals = fields
                    .iter()
                    .map(|(name, expr)| Ok((name.clone(), self.interpret_expr(expr)?)))
                    .collect::<Result<HashMap<String, Value>>>()?;
                Ok(Value::Struct(StructValue {
                    name: name.clone(),
                    fields: vals,
                }))
            }
            ExprKind::MemberAccess { target, member } => {
                let target_val = self.interpret_expr(target)?;
                match target_val {
                    Value::Struct(StructValue { fields, .. }) => fields
                        .get(member)
                        .cloned()
                        .ok_or_else(|| anyhow!("Field not found: {}", member)),
                    _ => Err(anyhow!("Member access must be done on a struct")),
                }
            }
        }
    }

    pub fn interpret_stmt(&mut self, stmt: &TypedStmt) -> Result<()> {
        match &stmt.node {
            TypedStmtKind::VarDecl(decl) => {
                let rhs = self.interpret_expr(&decl.value)?;
                self.call_stack.add_identifier(decl.name.clone(), rhs);
            }
            TypedStmtKind::Expr(expr) => {
                self.interpret_expr(expr)?;
            }
        }
        Ok(())
    }

    pub fn initialize_native_functions(&mut self) {
        for native_function in native_functions::get_native_functions() {
            self.globals.insert(
                native_function.name.clone(),
                Value::NativeFunction(native_function),
            );
        }
    }

    /**
     * Receives top level declarations and interprets them.
     */
    pub fn interpret(&mut self) -> Result<u8> {
        self.initialize_native_functions();
        let main = self
            .globals
            .get(MAIN_FUNCTION_NAME)
            .context("No main function found")?;
        let main_body = match main {
            Value::Function { body, .. } => {
                body.clone() // FIXME: borrow checker is not happy
            }
            _ => return Err(anyhow!("Main function must be a function")),
        };

        self.call_stack.push_call();
        let val = self.interpret_expr(&main_body)?;
        match val {
            Value::Integer(x) if (0..256).contains(&x) => Ok(x.try_into().unwrap()),
            Value::Integer(_) => Err(anyhow!(
                "Main function must return unit or integer between 0 and 255"
            )),
            Value::Unit => Ok(0),
            _ => Err(anyhow!("Main function must return integer or unit")),
        }
    }
}

pub fn decls_to_hashmap(decls: Vec<TypedDecl>) -> HashMap<String, TypedDecl> {
    let mut map = HashMap::new();
    for decl in decls {
        let name = match &decl.node {
            TypedDeclKind::FunDecl { name, .. } => name,
            TypedDeclKind::VarDecl(v) => &v.name,
            TypedDeclKind::StructDecl { name, .. } => name,
            TypedDeclKind::EnumDecl { name, .. } => name,
            TypedDeclKind::VariantConstructor { name, .. } => name,
        }
        .clone();
        map.insert(name, decl);
    }
    map
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::do_frontend_pass;

    #[test]
    fn test_interpret_main() {
        let ast = do_frontend_pass("fn main(): Int = 5").unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 5);

        let ast = do_frontend_pass("fn main(): Int = 1 + 2").unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 3);
    }

    #[test]
    fn test_interpreter_if() {
        let ast = do_frontend_pass("fn main(): Int = if true { 1 } else { 2 }").unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 1);

        let ast = do_frontend_pass("fn main(): Int = if false { 1 } else { 2 }").unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 2);
    }

    #[test]
    fn test_fact() {
        let ast = do_frontend_pass(
            "
fn fact(n: Int): Int = if n == 0 { 1 } else { n * fact(n - 1) }

fn main(): Int = fact(5)
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 120);
    }

    #[test]
    fn test_fib() {
        let ast = do_frontend_pass(
            "
fn fib(n: Int): Int = if n <= 1 { n } else { fib(n - 1) + fib(n - 2) }

fn main(): Int = fib(7)
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 13);
    }

    #[test]
    fn test_native_functions() {
        let ast = do_frontend_pass(
            "
fn main(): Int = pow(2, 3)
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 8);
    }

    #[test]
    fn test_compound_statements() {
        let ast = do_frontend_pass(
            "
fn main(): Int = {
    1;
    2
}
            ",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 2);

        let ast = do_frontend_pass(
            "
fn println[T](x: T): Bool = true

fn main(): Int = {
    println(2);
    1 + 2 + 3;
    4
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 4);
    }

    #[test]
    fn test_compound_decls() {
        let ast = do_frontend_pass(
            "
fn main(): Int = {
    let a: Int = 1;
    let b: Int = 2;
    a + b
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 3);
    }

    #[test]
    fn test_structs() {
        let ast = do_frontend_pass(
            "
struct Pair { x: Int, y: Int }

fn main(): Int = {
    let a: Pair = &Pair{x: 1, y: 2};
    a.x + a.y
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 3);
    }

    #[test]
    fn test_match_primitives() {
        let ast = do_frontend_pass(
            "
fn main(): Int = match 3 {
    2 => 5,
    3 => 7,
    _ => 9,
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 7);

        let ast = do_frontend_pass(
            "
fn main(): Int = match 3 {
    2 => 5,
    _ => 2,
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 2);

        let ast = do_frontend_pass(
            "
fn main(): Int = match true {
    true => 1,
    false => 2,
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 1);
    }

    #[test]
    fn test_match_enums() {
        let ast = do_frontend_pass(
            "
enum List {
    Cons(Int, List),
    Nil,
}

fn main(): Int = match Cons(1, Nil()) {
    Cons(x, y) => x,
    Nil() => 0,
}
",
        )
        .unwrap();

        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 1);
    }

    #[test]
    fn test_inner_match() {
        let ast = do_frontend_pass(
            "
enum List {
    Cons(Int, List),
    Nil,
}

fn main(): Int = match Cons(1, Cons(2, Nil())) {
    Cons(1, Cons(x, _)) => x,
    _ => 0,
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 2);
    }

    #[test]
    fn test_match_linked_list() {
        let ast = do_frontend_pass(
            "
enum List {
    Cons(Int, List),
    Nil,
}

fn max(lst: List): Int = match lst {
    Nil() => 0,
    Cons(head, tail) => {
        let max_tail = max(tail);
        if head > max_tail {
            head
        } else {
            max_tail
        }
    }
}

fn main(): Int = {
    let lst = Cons(1, Cons(3, Cons(2, Nil())));
    max(lst)
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 3);
    }

    #[test]
    fn test_match_struct() {
        let ast = do_frontend_pass(
            "
struct Pair { x: Int, y: Int }

fn main(): Int = match &Pair{x: 1, y: 2} {
    Pair{x, y} => x + y,
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 3);
    }

    #[test]
    fn test_match_cond() {
        let ast = do_frontend_pass(
            "
fn main(): Int = match 3 {
    x if x > 2 => 1,
    _ => 2,
}
",
        ).unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 1);

        let ast = do_frontend_pass(
            "
fn main(): Int = match 3 {
    x if x < 2 => 1,
    _ => 2,
}
",
        ).unwrap();
        let mut interpreter = Interpreter::new(decls_to_hashmap(ast));
        assert_eq!(interpreter.interpret().unwrap(), 2);
    }
}
