pub mod display;
pub mod pretty_print;

use std::fmt::Display;
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

/// We unfortunately need to separate LambdaFunDecl.
/// For untyped, it is FunDecl, and for typed, it is TypedFunDecl.
#[derive(Clone, Debug)]
pub enum ExprKind<St, Ex, LambdaFunDecl> {
    Unit,
    Int(i64),
    Boolean(bool),
    Char(char),
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
    Lambda(LambdaFunDecl),
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
pub struct Import {
    pub path: String,
    pub imported_ids: Vec<String>,
}

/// Represents single module, a single module maps to a single file.
/// This means that module is uniquely identified by its path.
#[derive(Clone, Debug)]
pub struct Module {
    pub decls: Vec<Decl>,
    pub imports: Vec<Import>,
}

#[derive(Clone, Debug)]
pub struct TypedModule {
    pub decls: Vec<TypedDecl>,
    pub imports: Vec<Import>,
}

#[derive(Clone, Debug)]
pub struct FunDecl {
    pub name: String,
    pub generics: Vec<GenericDeclaration>,
    pub parameters: Vec<WeaklyTypedIdentifier>,
    pub inferred_parameters: Option<Vec<Rc<InferredType>>>,
    pub return_type: Option<WrittenType>,
    pub inferred_return_type: Option<Rc<InferredType>>,
    pub body: Box<Expr>,
}

#[derive(Clone, Debug)]
pub enum DeclKind {
    FunDecl(FunDecl),
    StructDecl {
        name: String,
        generics: Vec<GenericDeclaration>,
        fields: Vec<StronglyTypedIdentifier>,
        /// This starts out empty when parsing, but is filled
        /// from the ImplDecl when typechecking.
        methods: Vec<FunDecl>,
    },
    EnumDecl {
        name: String,
        variants: Vec<EnumVariant>,
        generics: Vec<GenericDeclaration>,
        /// Same as StructDecl methods.
        methods: Vec<FunDecl>,
    },
    TraitDecl {
        name: String,
        methods: Vec<WeaklyTypedIdentifier>,
    },
    ImplDecl {
        target: String,
        generics: Vec<GenericDeclaration>,
        methods: Vec<FunDecl>,
    },
}

#[derive(Clone, Debug)]
pub struct TypedDecl {
    pub node: TypedDeclKind,
    pub location: Location,
}

#[derive(Clone, Debug)]
pub struct TypedFunDecl {
    pub name: String,
    pub parameters: Vec<TypedIdentifier>,
    pub return_type: InstantiatedType,
    pub body: Box<TypedExpr>,
}

#[derive(Clone, Debug)]
pub enum TypedDeclKind {
    FunDecl(TypedFunDecl),
    VarDecl(TypedVarDecl),
    StructDecl {
        name: String,
        fields: Vec<TypedIdentifier>,
        methods: Vec<TypedFunDecl>,
    },
    // Enum decls are important when interpreting,
    // because each variant is a constructor (function).
    EnumDecl {
        name: String,
        variants: Vec<EnumVariant>,
        methods: Vec<TypedFunDecl>,
    },
    // TODO: Isn't this useless?
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
    pub node: ExprKind<Stmt, Expr, FunDecl>,
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
    pub node: ExprKind<TypedStmt, TypedExpr, TypedFunDecl>,
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
            ExprKind::Lambda(fundecl) => {
                let body = Box::new(fundecl.body.fold(f_decl, f_stmt, f_expr)?);
                self.node = ExprKind::Lambda(FunDecl { body, ..fundecl });
            }
            // List them explicitly to avoid forgetting to implement them.
            ExprKind::Unit => (),
            ExprKind::Int(_) => (),
            ExprKind::Boolean(_) => (),
            ExprKind::Char(_) => (),
            ExprKind::Identifier(_) => (),
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
        match self.node {
            DeclKind::FunDecl(fun) => {
                let body = Box::new(fun.body.fold(f_decl, f_stmt, f_expr)?);
                self.node = DeclKind::FunDecl(FunDecl { body, ..fun });
            }
            DeclKind::StructDecl {
                name,
                generics,
                fields,
                methods,
            } => {
                let methods = methods
                    .into_iter()
                    .map(|fundecl| {
                        Ok(FunDecl {
                            body: Box::new(fundecl.body.fold(f_decl, f_stmt, f_expr)?),
                            ..fundecl
                        })
                    })
                    .collect::<Result<Vec<_>, E>>()?;
                self.node = DeclKind::StructDecl {
                    name,
                    generics,
                    fields,
                    methods,
                };
            }
            DeclKind::EnumDecl {
                name,
                variants,
                generics,
                methods,
            } => {
                let methods = methods
                    .into_iter()
                    .map(|fundecl| {
                        Ok(FunDecl {
                            body: Box::new(fundecl.body.fold(f_decl, f_stmt, f_expr)?),
                            ..fundecl
                        })
                    })
                    .collect::<Result<Vec<_>, E>>()?;
                self.node = DeclKind::EnumDecl {
                    name,
                    variants,
                    generics,
                    methods,
                };
            }
            DeclKind::TraitDecl { name, methods } => {
                unimplemented!("Traits are not yet implemented")
            }
            DeclKind::ImplDecl {
                target,
                generics,
                methods,
            } => todo!(),
        }
        if let DeclKind::FunDecl(FunDecl {
            name,
            generics,
            parameters,
            inferred_parameters,
            return_type,
            inferred_return_type,
            body,
        }) = self.node
        {
            let body = Box::new(body.fold(f_decl, f_stmt, f_expr)?);
            self.node = DeclKind::FunDecl(FunDecl {
                name,
                generics,
                parameters,
                inferred_parameters,
                return_type,
                inferred_return_type,
                body,
            });
        }
        f_decl(self)
    }
}
