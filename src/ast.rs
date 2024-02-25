use std::rc::Rc;

use crate::frontend::types::Type;
use crate::frontend::utils::{TypedIdentifier, WeaklyTypedIdentifier};

#[derive(Clone)]
pub struct Location {
    pub line: usize,
    pub column: usize,
}

impl Location {
    pub fn new(line: usize, column: usize) -> Location {
        Location { line, column }
    }
}

#[derive(Clone, Copy, PartialEq)]
pub enum Operator {
    Mul,
    Div,
    Add,
    Sub,
    Mod,
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    Equal,
    Neq,
}

impl From<&str> for Operator {
    fn from(value: &str) -> Self {
        match value {
            "*" => Operator::Mul,
            "/" => Operator::Div,
            "+" => Operator::Add,
            "-" => Operator::Sub,
            "%" => Operator::Mod,
            "<" => Operator::Less,
            ">" => Operator::Greater,
            "<=" => Operator::LessEqual,
            ">=" => Operator::GreaterEqual,
            "==" => Operator::Equal,
            "!=" => Operator::Neq,
            _ => panic!("Invalid operator"),
        }
    }
}

#[derive(Clone)]
pub enum ExprKind<St, Ex> {
    Unit,
    Int(i64),
    Boolean(bool),
    Identifier(String),
    Compound(Vec<St>, Box<Ex>),
    FunCall {
        target: Box<Ex>,
        args: Vec<Ex>,
    },
    If {
        cond: Box<Ex>,
        then: Box<Ex>,
        els: Box<Ex>,
    },
    Binary {
        op: Operator,
        lhs: Box<Ex>,
        rhs: Box<Ex>,
    },
}

#[derive(Clone)]
pub enum StmtKind {
    VarDecl(VarDecl),
    Expr(Expr),
}

#[derive(Clone)]
pub struct Decl {
    pub node: DeclKind,
    pub location: Location,
}

// Untyped

#[derive(Clone)]
pub struct VarDecl {
    pub name: String,
    pub ty: Option<String>,
    pub value: Box<Expr>,
}

#[derive(Clone)]
pub struct TypedVarDecl {
    pub name: String,
    pub value: Box<TypedExpr>,
}

#[derive(Clone)]
pub enum DeclKind {
    FunDecl {
        name: String,
        parameters: Vec<WeaklyTypedIdentifier>,
        return_type: Option<String>,
        body: Box<Expr>,
    },
    #[allow(dead_code)]
    VarDecl(VarDecl),
    #[allow(dead_code)]
    StructDecl {
        name: String,
        fields: Vec<WeaklyTypedIdentifier>,
    },
    // We allow writing variants similar to structs.
    #[allow(dead_code)]
    EnumDecl {
        name: String,
        variants: Vec<WeaklyTypedIdentifier>,
    },
    #[allow(dead_code)]
    TraitDecl {
        name: String,
        methods: Vec<WeaklyTypedIdentifier>,
    },
}

pub struct TypedDecl {
    pub node: TypedDeclKind,
    pub location: Location,
}

#[derive(Clone)]
pub enum TypedDeclKind {
    FunDecl {
        name: String,
        parameters: Vec<TypedIdentifier>,
        return_type: Rc<Type>,
        body: Box<TypedExpr>,
    },
    #[allow(dead_code)]
    VarDecl(TypedVarDecl),
}

#[derive(Clone)]
pub struct Expr {
    pub node: ExprKind<Stmt, Expr>,
    pub location: Location,
}

#[derive(Clone)]
pub struct Stmt {
    pub node: StmtKind,
    pub location: Location,
}

#[derive(Clone)]
pub struct TypedExpr {
    pub node: ExprKind<TypedStmt, TypedExpr>,
    pub location: Location,
    pub ty: Rc<Type>,
}

#[derive(Clone)]
pub struct TypedStmt {
    pub node: TypedStmtKind,
    pub location: Location,
}

#[derive(Clone)]
pub enum TypedStmtKind {
    VarDecl(TypedVarDecl),
    Expr(TypedExpr),
}
