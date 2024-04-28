use anyhow::{anyhow, Context, Result};
use std::fmt::{self, Display, Formatter};
use std::{collections::HashMap, rc::Rc};

use crate::ast::{
    ExprKind, Import, Operator, Pattern, TypedDecl, TypedDeclKind, TypedExpr, TypedModule,
    TypedStmt, TypedStmtKind,
};

use super::native_functions;
use super::native_functions::NativeFunction;
use crate::constants::STD_NATIVE_MODULE;

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
        /// Which module the function is defined in
        module: String,
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
    /// Each item in the vector is a new layer of scope
    env: Vec<HashMap<String, Value>>,
    /// The current module that is being interpreted
    /// To know from where to take globals.
    current_module: String,
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
    /// For each call, there is a new CallEnvironment
    stack: Vec<CallEnvironment>,
}

impl CallStack {
    pub fn new() -> CallStack {
        CallStack { stack: vec![] }
    }

    /// Pushes a new call environment to the stack with one layer.
    pub fn push_call(&mut self, current_module: String) {
        self.stack.push(CallEnvironment {
            env: vec![HashMap::new()],
            current_module,
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

    pub fn get_current_module(&self) -> &str {
        &self
            .stack
            .last()
            .expect("No environment, use push first!")
            .current_module
    }
}

struct Globals {
    /// module -> declaration name -> value
    /// For each module, there is a HashMap from name to value.
    /// Previously, we had (name, value) -> module, but this way
    /// we can use &str as keys and not have to clone strings.
    /// TODO: Check if the hashmap in hashmap is not worse.
    globals: HashMap<String, HashMap<String, Value>>,
}

impl Globals {
    pub fn new() -> Globals {
        Globals {
            globals: HashMap::new(),
        }
    }

    pub fn add(&mut self, module: String, name: String, value: Value) {
        let module = self.globals.entry(module).or_insert(HashMap::new());
        module.insert(name, value);
    }

    pub fn get(&self, module: &str, name: &str) -> Option<&Value> {
        self.globals.get(module).and_then(|m| m.get(name))
    }

    /// Searches through all modules for given value (declaration)
    /// Returns vector with (Module name, value)
    pub fn find(&self, to_find: &str) -> Vec<(String, &Value)> {
        self.globals.iter().fold(vec![], |mut acc, (name, module)| {
            if let Some(main) = module.get(to_find) {
                acc.push((name.clone(), main));
            }
            acc
        })
    }
}

/// Extracts name from each declaration and returns it as hashmap.
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

/// Contains HashMap from name of declaration to declaration, contrary
/// to TypedModule which contains Vec of declarations.
pub struct NamedModule {
    decls: HashMap<String, TypedDecl>,
    imports: Vec<Import>,
}

impl From<TypedModule> for NamedModule {
    fn from(module: TypedModule) -> Self {
        NamedModule {
            decls: decls_to_hashmap(module.decls),
            imports: module.imports,
        }
    }
}

pub struct Interpreter {
    call_stack: CallStack,
    globals: Globals,
    modules: HashMap<String, NamedModule>,
}

impl Interpreter {
    pub fn new(modules: HashMap<String, NamedModule>) -> Self {
        let mut globals = Globals::new();
        for (module_name, module) in modules.iter() {
            for (name, decl) in module.decls.iter() {
                let val = match &decl.node {
                    TypedDeclKind::FunDecl {
                        body, parameters, ..
                    } => Some(Value::Function {
                        body: *body.clone(),
                        parameters: parameters.iter().map(|p| p.name.clone()).collect(),
                        module: module_name.clone(),
                    }),
                    TypedDeclKind::EnumDecl { variants, .. } => {
                        for variant in variants {
                            let param_cnt = variant.fields.len();
                            let name = variant.name.clone();
                            let cons = Value::Constructor {
                                name: name.clone(),
                                param_cnt,
                            };
                            globals.add(module_name.clone(), name, cons);
                        }
                        None
                    }
                    _ => None,
                };
                if let Some(value) = val {
                    globals.add(module_name.clone(), name.clone(), value);
                }
            }
        }
        Interpreter {
            call_stack: CallStack::new(),
            globals,
            modules,
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

    pub fn get_current_module(&self) -> &NamedModule {
        let name = self.call_stack.get_current_module();
        self.modules.get(name).expect("Module not found")
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
                    value = self.globals.get(self.call_stack.get_current_module(), id);
                }
                if value.is_none() {
                    value = self
                        .get_current_module()
                        .imports
                        .iter()
                        .find(|import| import.imported_ids.contains(id))
                        .and_then(|import| self.globals.get(&import.path, id));
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

                let resulting_function = self.interpret_expr(target)?;
                match resulting_function {
                    Value::Function { module, body, parameters } => {
                        self.call_stack.push_call(module);
                        for (param, arg) in parameters.iter().zip(args_values.iter()) {
                            self.call_stack.add_identifier(param.clone(), arg.clone());
                        }
                        let result = self.interpret_expr(&body)?;
                        self.call_stack.pop_call();
                        Ok(result)
                    },
                    Value::NativeFunction(NativeFunction{body, ..}) => {
                        let result = body(args_values)?;
                        Ok(result)
                    },
                    Value::Constructor{name, param_cnt: _} => {
                        let result = Value::Variant {
                            name,
                            fields: Rc::new(args_values),
                        };
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
            self.globals.add(
                STD_NATIVE_MODULE.to_string(),
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

        let mains = self.globals.find(MAIN_FUNCTION_NAME);
        if mains.is_empty() {
            return Err(anyhow!("No main function found"));
        } else if mains.len() != 1 {
            return Err(anyhow!("Multiple declarations with the 'main' name found. There must be only one and it must be a function."));
        }

        let main_module = mains[0].0.clone(); // TODO: Ugly, but cant simply do (x, y) = mains[0], since one is ref.
        let main = mains[0].1;

        let main_body = match main {
            Value::Function { body, .. } => {
                body.clone() // FIXME: borrow checker is not happy
            }
            _ => return Err(anyhow!("Main function must be a function")),
        };

        self.call_stack.push_call(main_module);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::fe_pass;

    fn fe_pass_one_file(code: &str) -> Result<HashMap<String, NamedModule>> {
        let mut modules = HashMap::new();
        modules.insert("main".to_string(), code.to_string());
        let typed = fe_pass(modules)?;
        Ok(typed
            .into_iter()
            .map(|(name, module)| (name, NamedModule::from(module)))
            .collect())
    }

    #[test]
    fn test_interpret_main() {
        let ast = fe_pass_one_file("fn main(): Int = 5").unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 5);

        let ast = fe_pass_one_file("fn main(): Int = 1 + 2").unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 3);
    }

    #[test]
    fn test_interpreter_if() {
        let ast = fe_pass_one_file("fn main(): Int = if true { 1 } else { 2 }").unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 1);

        let ast = fe_pass_one_file("fn main(): Int = if false { 1 } else { 2 }").unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 2);
    }

    #[test]
    fn test_fact() {
        let ast = fe_pass_one_file(
            "
fn fact(n: Int): Int = if n == 0 { 1 } else { n * fact(n - 1) }

fn main(): Int = fact(5)
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 120);
    }

    #[test]
    fn test_fib() {
        let ast = fe_pass_one_file(
            "
fn fib(n: Int): Int = if n <= 1 { n } else { fib(n - 1) + fib(n - 2) }

fn main(): Int = fib(7)
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 13);
    }

    #[test]
    fn test_native_functions() {
        let ast = fe_pass_one_file(
            "
import { pow } from \"std/internal/native\";

fn main(): Int = pow(2, 3)
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 8);
    }

    #[test]
    fn test_compound_statements() {
        let ast = fe_pass_one_file(
            "
fn main(): Int = {
    1;
    2
}
            ",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 2);

        let ast = fe_pass_one_file(
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
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 4);
    }

    #[test]
    fn test_compound_decls() {
        let ast = fe_pass_one_file(
            "
fn main(): Int = {
    let a: Int = 1;
    let b: Int = 2;
    a + b
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 3);
    }

    #[test]
    fn test_structs() {
        let ast = fe_pass_one_file(
            "
struct Pair { x: Int, y: Int }

fn main(): Int = {
    let a: Pair = &Pair{x: 1, y: 2};
    a.x + a.y
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 3);
    }

    #[test]
    fn test_match_primitives() {
        let ast = fe_pass_one_file(
            "
fn main(): Int = match 3 {
    2 => 5,
    3 => 7,
    _ => 9,
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 7);

        let ast = fe_pass_one_file(
            "
fn main(): Int = match 3 {
    2 => 5,
    _ => 2,
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 2);

        let ast = fe_pass_one_file(
            "
fn main(): Int = match true {
    true => 1,
    false => 2,
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 1);
    }

    #[test]
    fn test_match_enums() {
        let ast = fe_pass_one_file(
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

        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 1);
    }

    #[test]
    fn test_inner_match() {
        let ast = fe_pass_one_file(
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
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 2);
    }

    #[test]
    fn test_match_linked_list() {
        let ast = fe_pass_one_file(
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
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 3);
    }

    #[test]
    fn test_match_struct() {
        let ast = fe_pass_one_file(
            "
struct Pair { x: Int, y: Int }

fn main(): Int = match &Pair{x: 1, y: 2} {
    Pair{x, y} => x + y,
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 3);
    }

    #[test]
    fn test_match_cond() {
        let ast = fe_pass_one_file(
            "
fn main(): Int = match 3 {
    x if x > 2 => 1,
    _ => 2,
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 1);

        let ast = fe_pass_one_file(
            "
fn main(): Int = match 3 {
    x if x < 2 => 1,
    _ => 2,
}
",
        )
        .unwrap();
        let mut interpreter = Interpreter::new(ast);
        assert_eq!(interpreter.interpret().unwrap(), 2);
    }

    #[test]
    fn test_modules() {
        let ast1 = "
import { foo } from \"foo\";
import { bar, baz } from \"baz\";

fn main(): Int = {
    let x = foo(bar(), baz(1));
    x
}
            ";

        let ast2 = "
fn foo(x: Int, y: Int): Int = x + y
";

        let ast3 = "
fn bar(): Int = 1
fn baz(x: Int): Int = x + 1
";
        let mut modules = HashMap::new();
        modules.insert("main".to_string(), ast1.to_string());
        modules.insert("foo".to_string(), ast2.to_string());
        modules.insert("baz".to_string(), ast3.to_string());
        let typed = fe_pass(modules).unwrap();
        let mut interpreter = Interpreter::new(
            typed
                .into_iter()
                .map(|(name, module)| (name, NamedModule::from(module)))
                .collect(),
        );
        assert_eq!(interpreter.interpret().unwrap(), 3);
    }
}
