use std::rc::Rc;

use crate::frontend::types::Type;

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

#[derive(Clone)]
pub enum ExprKind<St, Ex> {
    Int(i64),
    Identifier(String),
    Compound(Vec<St>, Box<Ex>),
}

#[derive(Clone)]
pub enum StmtKind {
    VarDecl {
        name: String,
        ty: Option<String>,
        value: Option<Expr>,
    },
}

#[derive(Clone)]
pub struct Decl {
    pub node: DeclKind,
    pub location: Location,
}

#[derive(Clone)]
pub struct WeaklyTypedIdentifier {
    pub name: String,
    pub ty: Option<String>,
}

#[derive(Clone)]
pub struct TypedIdentifier {
    pub name: String,
    pub ty: Rc<Type>,
}

// Untyped

#[derive(Clone)]
pub enum DeclKind {
    FunDecl {
        name: String,
        parameters: Vec<WeaklyTypedIdentifier>,
        return_type: Option<String>,
        body: Box<Expr>,
    },
    StructDecl {
        name: String,
        fields: Vec<WeaklyTypedIdentifier>,
    },
    // We allow writing variants similar to structs.
    EnumDecl {
        name: String,
        variants: Vec<WeaklyTypedIdentifier>,
    },
    TraitDecl {
        name: String,
        methods: Vec<WeaklyTypedIdentifier>,
    },
}

pub struct TypedDecl {
    pub node: TypedDeclKind,
    pub location: Location,
}

pub enum TypedDeclKind {
    FunDecl {
        name: String,
        parameters: Vec<TypedIdentifier>,
        return_type: Rc<Type>,
        body: Box<TypedExpr>,
    },
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

pub struct TypedExpr {
    pub node: ExprKind<Stmt, TypedExpr>,
    pub location: Location,
    pub ty: Rc<Type>,
}
