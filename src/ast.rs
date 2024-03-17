pub mod display;
pub mod pretty_print;

use std::fmt::{Display, Formatter};
use std::rc::Rc;

use crate::frontend::type_inference::Type as InferredType;
use crate::frontend::types::InstantiatedType;
use crate::frontend::utils::{
    GenericDeclaration, StronglyTypedIdentifier, TypedIdentifier, WeaklyTypedIdentifier,
    WrittenType,
};

#[derive(Clone, Debug)]
pub struct Location {
    pub line: usize,
    pub column: usize,
}

impl Location {
    pub fn new(line: usize, column: usize) -> Location {
        Location { line, column }
    }
}

#[derive(Clone, Debug, Copy, PartialEq)]
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

#[derive(Clone, Debug)]
pub struct MatchArm<Ex> {
    pub pattern: Pattern,
    pub cond: Option<Box<Ex>>,
    pub body: Box<Ex>,
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Wildcard, // _
    Int(i64),
    Boolean(bool),
    String(String),
    // Foo{foo, bar}
    Struct {
        name: String,
        fields: Vec<String>,
    },
    // Foo(Bar(Int), String)
    Enum {
        name: String,
        patterns: Vec<Pattern>,
    },
    Identifier(String),
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Wildcard => write!(f, "_"),
            Pattern::Int(x) => write!(f, "{}", x),
            Pattern::Boolean(x) => write!(f, "{}", x),
            Pattern::String(x) => write!(f, "{}", x),
            Pattern::Struct { name, fields } => {
                let fields_str = fields.join(", ");
                write!(f, "{} {{{}}}", name, fields_str)?;
                Ok(())
            }
            Pattern::Enum { name, patterns } => {
                let patterns_str = patterns
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}({})", name, patterns_str)?;
                Ok(())
            }
            Pattern::Identifier(x) => write!(f, "{}", x),
        }
    }
}

#[derive(Clone, Debug)]
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
    Match {
        target: Box<Ex>,
        arms: Vec<MatchArm<Ex>>,
    },
    StructInitializer {
        name: String,
        fields: Vec<(String, Ex)>,
        generics: Vec<WrittenType>,
    },
    MemberAccess {
        target: Box<Ex>,
        member: String,
    },
}

#[derive(Clone, Debug)]
pub enum StmtKind {
    VarDecl(VarDecl),
    Expr(Expr),
}

#[derive(Clone, Debug)]
pub struct Decl {
    pub node: DeclKind,
    pub location: Location,
    // Saved after type inference.
    pub inferred_ty: Option<InferredType>,
}

impl Decl {
    pub fn new(node: DeclKind, location: Location) -> Decl {
        Decl {
            node,
            location,
            inferred_ty: None,
        }
    }
}

impl Display for Decl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.node {
            DeclKind::FunDecl {
                name,
                generics,
                parameters,
                return_type,
                body,
                inferred_parameters,
                inferred_return_type,
            } => {
                write!(f, "fn {}", name)?;

                if !generics.is_empty() {
                    write!(f, "<")?;
                    let generics: Vec<String> = generics.iter().map(|x| x.to_string()).collect();
                    write!(f, "{}", generics.join(", "))?;
                    write!(f, ">")?;
                }

                let params: Vec<String> = if let Some(inferred_parameters) = inferred_parameters {
                    inferred_parameters
                        .iter()
                        .zip(parameters)
                        .map(|(ty, name)| format!("{}: {}", name.name, ty))
                        .collect()
                } else {
                    parameters.iter().map(|x| x.to_string()).collect()
                };
                write!(f, "({})", params.join(", "))?;
                if let Some(t) = inferred_return_type {
                    write!(f, ": {}", t)?;
                } else if let Some(t) = return_type {
                    write!(f, ": {}", t)?;
                }

                write!(f, " = {}", body)
            }
            DeclKind::StructDecl { .. } => todo!(),
            DeclKind::EnumDecl {
                name,
                variants,
                generics,
            } => {
                write!(f, "enum {}", name)?;
                let generics = generics
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                if !generics.is_empty() {
                    write!(f, "<{}>", generics)?;
                }

                write!(f, " {{")?;
                let variants = variants
                    .iter()
                    .map(|variant| {
                        let fields = variant
                            .fields
                            .iter()
                            .map(|x| x.to_string())
                            .collect::<Vec<String>>()
                            .join(", ");
                        format!("{}({})", variant.name, fields)
                    })
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}", variants)?;
                write!(f, "}}")
            }
            DeclKind::TraitDecl { .. } => todo!(),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.node)
    }
}

impl<A, B> Display for ExprKind<A, B>
where
    A: Display,
    B: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprKind::Unit => write!(f, "()"),
            ExprKind::Int(x) => write!(f, "{}", x),
            ExprKind::Boolean(x) => write!(f, "{}", x),
            ExprKind::Identifier(x) => write!(f, "{}", x),
            ExprKind::Compound(stmts, expr) => {
                write!(f, "{{ ")?;
                for stmt in stmts {
                    write!(f, "{}; ", stmt)?;
                }
                write!(f, "{} ", expr)?;
                write!(f, "}}")
            }
            ExprKind::FunCall { target, args } => {
                write!(f, "{}", target)?;
                write!(f, "(")?;
                let mut first = true;

                for arg in args {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }

                write!(f, ")")
            }
            ExprKind::If { cond, then, els } => {
                write!(f, "if {} {{ {} }} else {{ {} }}", cond, then, els)
            }
            ExprKind::Binary { op, lhs, rhs } => {
                write!(f, "({} {} {})", lhs, op, rhs)
            }
            ExprKind::Match { target, arms } => {
                write!(f, "match {} {{", target)?;
                let arms = arms
                    .iter()
                    .map(|arm| arm.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}", arms)?;
                write!(f, "}}")
            }
            ExprKind::StructInitializer {
                name,
                fields,
                generics,
            } => {
                let generics = generics
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                let generics = if generics.is_empty() {
                    "".to_string()
                } else {
                    format!("[{}]", generics)
                };
                let fields = fields
                    .iter()
                    .map(|(field, expr)| format!("{}: {}", field, expr))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}{} {{ {} }}", name, generics, fields)
            }
            ExprKind::MemberAccess { target, member } => {
                write!(f, "{}.{}", target, member)
            }
        }
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.node)
    }
}

impl Display for StmtKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            StmtKind::VarDecl(decl) => {
                write!(f, "let {}", decl.name)?;
                if let Some(inferred_ty) = &decl.inferred_ty {
                    write!(f, ": {}", inferred_ty)?;
                } else if let Some(ty) = &decl.ty {
                    write!(f, ": {}", ty)?;
                }
                write!(f, " = {}", decl.value)
            }
            StmtKind::Expr(expr) => write!(f, "{}", expr),
        }
    }
}

impl<T> Display for MatchArm<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "case {} => {}", self.pattern, self.body)
    }
}

impl Display for Operator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Operator::Mul => " * ".fmt(f),
            Operator::Div => " / ".fmt(f),
            Operator::Add => " + ".fmt(f),
            Operator::Sub => " - ".fmt(f),
            Operator::Mod => " % ".fmt(f),
            Operator::Less => " < ".fmt(f),
            Operator::Greater => " > ".fmt(f),
            Operator::LessEqual => " <= ".fmt(f),
            Operator::GreaterEqual => " >= ".fmt(f),
            Operator::Equal => " == ".fmt(f),
            Operator::Neq => " != ".fmt(f),
        }
    }
}

// Untyped

#[derive(Clone, Debug)]
pub struct VarDecl {
    pub name: String,
    pub ty: Option<WrittenType>,
    pub value: Box<Expr>,
    // Saved after type inference.
    pub inferred_ty: Option<InferredType>,
}

#[derive(Clone, Debug)]
pub struct TypedVarDecl {
    pub name: String,
    pub value: Box<TypedExpr>,
}

#[derive(Clone, Debug)]
pub struct EnumVariant {
    pub name: String,
    pub fields: Vec<WrittenType>,
}

#[derive(Clone, Debug)]
pub enum DeclKind {
    FunDecl {
        name: String,
        generics: Vec<GenericDeclaration>,
        parameters: Vec<WeaklyTypedIdentifier>,
        inferred_parameters: Option<Vec<Rc<InferredType>>>,
        return_type: Option<WrittenType>,
        inferred_return_type: Option<Rc<InferredType>>,
        body: Box<Expr>,
    },
    StructDecl {
        name: String,
        generics: Vec<GenericDeclaration>,
        fields: Vec<StronglyTypedIdentifier>,
    },
    EnumDecl {
        name: String,
        variants: Vec<EnumVariant>,
        generics: Vec<GenericDeclaration>,
    },
    TraitDecl {
        name: String,
        methods: Vec<WeaklyTypedIdentifier>,
    },
}

#[derive(Clone, Debug)]
pub struct TypedDecl {
    pub node: TypedDeclKind,
    pub location: Location,
}

#[derive(Clone, Debug)]
pub enum TypedDeclKind {
    FunDecl {
        name: String,
        parameters: Vec<TypedIdentifier>,
        return_type: InstantiatedType,
        body: Box<TypedExpr>,
    },
    VarDecl(TypedVarDecl),
    StructDecl {
        name: String,
        fields: Vec<TypedIdentifier>,
    },
    // Enum decls are important when interpreting,
    // because each variant is a constructor (function).
    EnumDecl {
        name: String,
        variants: Vec<EnumVariant>,
    },
    VariantConstructor {
        name: String,
        // We don't need types here, because they are already
        // stored in the enum decl. This is only used when
        // interpreting and then the types are already correct.
        fields_count: usize,
    },
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub node: ExprKind<Stmt, Expr>,
    pub location: Location,
    pub inferred_ty: Option<Rc<InferredType>>,
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub node: StmtKind,
    pub location: Location,
}

#[derive(Clone, Debug)]
pub struct TypedExpr {
    pub node: ExprKind<TypedStmt, TypedExpr>,
    pub location: Location,
    pub ty: InstantiatedType,
}

#[derive(Clone, Debug)]
pub struct TypedStmt {
    pub node: TypedStmtKind,
    pub location: Location,
}

#[derive(Clone, Debug)]
pub enum TypedStmtKind {
    VarDecl(TypedVarDecl),
    Expr(TypedExpr),
}

impl Stmt {
    pub fn fold<E>(
        mut self,
        f_decl: &impl Fn(Decl) -> Result<Decl, E>,
        f_stmt: &impl Fn(Stmt) -> Result<Stmt, E>,
        f_expr: &impl Fn(Expr) -> Result<Expr, E>,
    ) -> Result<Self, E> {
        self.node = match self.node {
            StmtKind::VarDecl(decl) => {
                let value = Box::new(decl.value.fold(f_decl, f_stmt, f_expr)?);
                StmtKind::VarDecl(VarDecl {
                    name: decl.name,
                    ty: decl.ty,
                    value,
                    inferred_ty: decl.inferred_ty,
                })
            }
            StmtKind::Expr(expr) => StmtKind::Expr(expr.fold(f_decl, f_stmt, f_expr)?),
        };
        f_stmt(self)
    }
}

impl Expr {
    pub fn fold<E>(
        mut self,
        f_decl: &impl Fn(Decl) -> Result<Decl, E>,
        f_stmt: &impl Fn(Stmt) -> Result<Stmt, E>,
        f_expr: &impl Fn(Expr) -> Result<Expr, E>,
    ) -> Result<Self, E> {
        match self.node {
            ExprKind::Compound(stmts, expr) => {
                let stmts = stmts
                    .into_iter()
                    .map(|stmt| stmt.fold(f_decl, f_stmt, f_expr))
                    .collect::<Result<Vec<_>, E>>()?;
                let expr = Box::new(expr.fold(f_decl, f_stmt, f_expr)?);
                self.node = ExprKind::Compound(stmts, expr);
            }
            ExprKind::FunCall { target, args } => {
                let target = Box::new(target.fold(f_decl, f_stmt, f_expr)?);
                let args = args
                    .into_iter()
                    .map(|arg| arg.fold(f_decl, f_stmt, f_expr))
                    .collect::<Result<Vec<_>, E>>()?;
                self.node = ExprKind::FunCall { target, args };
            }
            ExprKind::If { cond, then, els } => {
                let cond = Box::new(cond.fold(f_decl, f_stmt, f_expr)?);
                let then = Box::new(then.fold(f_decl, f_stmt, f_expr)?);
                let els = Box::new(els.fold(f_decl, f_stmt, f_expr)?);
                self.node = ExprKind::If { cond, then, els };
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let lhs = Box::new(lhs.fold(f_decl, f_stmt, f_expr)?);
                let rhs = Box::new(rhs.fold(f_decl, f_stmt, f_expr)?);
                self.node = ExprKind::Binary { op, lhs, rhs };
            }
            ExprKind::Match { target, arms } => {
                let target = Box::new(target.fold(f_decl, f_stmt, f_expr)?);
                let arms = arms
                    .into_iter()
                    .map(
                        |MatchArm {
                             pattern,
                             cond,
                             body,
                         }| {
                            let cond = match cond {
                                Some(cond) => Some(Box::new(cond.fold(f_decl, f_stmt, f_expr)?)),
                                None => None,
                            };
                            let body = Box::new(body.fold(f_decl, f_stmt, f_expr)?);
                            Ok(MatchArm {
                                pattern,
                                cond,
                                body,
                            })
                        },
                    )
                    .collect::<Result<Vec<_>, _>>()?;
                self.node = ExprKind::Match { target, arms };
            }
            ExprKind::StructInitializer {
                name,
                fields,
                generics,
            } => {
                let mut new_fields = vec![];
                for (field, expr) in fields {
                    let expr = expr.fold(f_decl, f_stmt, f_expr)?;
                    new_fields.push((field, expr));
                }
                self.node = ExprKind::StructInitializer {
                    name,
                    fields: new_fields,
                    generics,
                };
            }
            ExprKind::MemberAccess { target, member } => {
                let target = Box::new(target.fold(f_decl, f_stmt, f_expr)?);
                self.node = ExprKind::MemberAccess { target, member };
            }
            _ => (),
        };
        f_expr(self)
    }
}

impl Decl {
    pub fn fold<E>(
        mut self,
        f_decl: &impl Fn(Decl) -> Result<Decl, E>,
        f_stmt: &impl Fn(Stmt) -> Result<Stmt, E>,
        f_expr: &impl Fn(Expr) -> Result<Expr, E>,
    ) -> Result<Self, E> {
        if let DeclKind::FunDecl { name, generics, parameters, inferred_parameters, return_type, inferred_return_type, body } = self.node {
            let body = Box::new(body.fold(f_decl, f_stmt, f_expr)?);
            self.node = DeclKind::FunDecl { name, generics, parameters, inferred_parameters, return_type, inferred_return_type, body };
        }
        f_decl(self)
    }
}
