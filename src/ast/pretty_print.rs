use crate::ast::*;
use crate::traits::PrettyPrint;
use std::fmt::Display;
use std::fmt::{Error, Formatter};

pub struct PrettyPrintWrapper<'a, T>(&'a T)
where
    T: PrettyPrint;

impl Display for PrettyPrintWrapper<'_, DeclKind> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        self.0.pretty_print(f, 0)
    }
}

impl Display for PrettyPrintWrapper<'_, TypedDeclKind> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        self.0.pretty_print(f, 0)
    }
}

fn print_spaces(f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error> {
    write!(f, "{}", " ".repeat(spaces as usize))
}

impl PrettyPrint for DeclKind {
    fn pretty_print(&self, f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error> {
        match self {
            DeclKind::FunDecl {
                name,
                generics,
                inferred_parameters,
                return_type,
                inferred_return_type,
                body,
                ..
            } => {
                write!(f, "fn {}", name)?;
                let generics = generics
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                if !generics.is_empty() {
                    write!(f, "[{}]", generics)?;
                }

                write!(f, "(")?;
                let parameters = inferred_parameters
                    .iter()
                    .map(|p| {
                        p.iter()
                            .map(|r| r.to_string())
                            .collect::<Vec<String>>()
                            .join(", ")
                    })
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}", parameters)?;
                write!(f, ")")?;

                if let Some(t) = inferred_return_type {
                    write!(f, ": {} = ", t)?;
                } else if let Some(return_type) = return_type {
                    write!(f, ": {} = ", return_type)?;
                }

                body.pretty_print(f, spaces + 4)?;
                Ok(())
            }
            DeclKind::StructDecl {
                name,
                generics,
                fields,
            } => {
                write!(f, "struct {}", name)?;
                let generics = generics
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                if !generics.is_empty() {
                    write!(f, "[{}]", generics)?;
                }

                writeln!(f, " {{")?;
                for field in fields {
                    write!(f, "{}", field)?;
                    writeln!(f)?;
                }
                writeln!(f, "}}")
            }
            DeclKind::EnumDecl {
                name,
                variants,
                generics,
            } => {
                write!(f, "enum {}", name)?;
                let generics = generics
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                if !generics.is_empty() {
                    write!(f, "[{}]", generics)?;
                }

                writeln!(f, " {{")?;
                for variant in variants {
                    print_spaces(f, spaces + 4)?;
                    write!(f, "{}", variant)?;
                    writeln!(f)?;
                }

                write!(f, "}}")
            }
            DeclKind::TraitDecl { .. } => todo!(),
        }
    }
}

impl PrettyPrint for TypedDeclKind {
    fn pretty_print(&self, f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error> {
        match self {
            TypedDeclKind::FunDecl {
                name,
                parameters,
                return_type,
                body,
            } => {
                write!(f, "fn {}(", name)?;
                let parameters = parameters
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}): {} = ", parameters, return_type)?;
                body.pretty_print(f, spaces + 4)
            }
            TypedDeclKind::VarDecl(TypedVarDecl { name, value }) => {
                write!(f, "let {}: {} = ", name, value.ty)?;
                value.pretty_print(f, spaces)
            }
            TypedDeclKind::StructDecl { name, fields } => {
                write!(f, "struct {}", name)?;
                writeln!(f, " {{")?;
                for TypedIdentifier { name, ty } in fields {
                    print_spaces(f, spaces + 4)?;
                    write!(f, "{}: {}", name, ty)?;
                    writeln!(f)?;
                }
                write!(f, "}}")
            }
            TypedDeclKind::EnumDecl { name, variants } => {
                write!(f, "enum {} {{", name)?;
                for variant in variants {
                    print_spaces(f, spaces + 4)?;
                    write!(f, "{}", variant)?;
                }
                write!(f, "}}")
            }
            // Do not print anything for these guys
            TypedDeclKind::VariantConstructor { .. } => Ok(()),
        }
    }
}

impl<S, E> PrettyPrint for ExprKind<S, E>
where
    S: PrettyPrint + Display,
    E: PrettyPrint + Display,
{
    fn pretty_print(&self, f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error> {
        match self {
            ExprKind::Unit => write!(f, "()"),
            ExprKind::Int(v) => write!(f, "{}", v),
            ExprKind::Boolean(v) => write!(f, "{}", v),
            ExprKind::Char(v) => write!(f, "{}", v),
            ExprKind::Identifier(i) => write!(f, "{}", i),
            ExprKind::Compound(stmts, expr) => {
                if stmts.is_empty() {
                    write!(f, "{{")?;
                    expr.pretty_print(f, spaces)?;
                    write!(f, "}}")
                } else {
                    writeln!(f, "{{")?;
                    for stmt in stmts {
                        print_spaces(f, spaces)?;
                        stmt.pretty_print(f, spaces + 4)?;
                        writeln!(f)?;
                    }
                    print_spaces(f, spaces)?;
                    expr.pretty_print(f, spaces + 4)?;
                    writeln!(f)?;
                    write!(f, "}}")
                }
            }
            ExprKind::FunCall { target, args } => {
                target.pretty_print(f, spaces)?;
                write!(f, "(")?;
                let args = args
                    .iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}", args)?;
                write!(f, ")")
            }
            ExprKind::If { cond, then, els } => {
                write!(f, "if ")?;
                cond.pretty_print(f, spaces)?;
                write!(f, " ")?;
                then.pretty_print(f, spaces)?;
                write!(f, " else ")?;
                els.pretty_print(f, spaces)?;
                Ok(())
            }
            ExprKind::Binary { op, lhs, rhs } => {
                lhs.pretty_print(f, spaces)?;
                write!(f, " {} ", op)?;
                rhs.pretty_print(f, spaces)
            }
            ExprKind::Match { target, arms } => {
                write!(f, "match ")?;
                target.pretty_print(f, spaces)?;
                writeln!(f, " {{")?;
                for arm in arms {
                    print_spaces(f, spaces)?;
                    write!(f, "{} => ", arm.pattern)?;
                    arm.body.pretty_print(f, spaces + 4)?;
                    writeln!(f)?;
                }
                print_spaces(f, spaces - 4)?;
                write!(f, "}}")
            }
            ExprKind::StructInitializer {
                name,
                fields,
                generics,
            } => {
                let generics = generics
                    .iter()
                    .map(|wt| format!("{}", wt))
                    .collect::<Vec<String>>()
                    .join(", ");
                let generics = if generics.is_empty() {
                    "".to_string()
                } else {
                    format!("[{}]", generics)
                };
                writeln!(f, "{}{} {{", name, generics)?;
                for field in fields {
                    print_spaces(f, spaces + 4)?;
                    write!(f, "{}: ", field.0)?;
                    field.1.pretty_print(f, spaces + 4)?;
                    writeln!(f)?;
                }
                write!(f, "}}")
            }
            ExprKind::MemberAccess { target, member } => {
                target.pretty_print(f, spaces)?;
                write!(f, ".{}", member)
            }
        }
    }
}

impl PrettyPrint for StmtKind {
    fn pretty_print(&self, f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error> {
        match self {
            StmtKind::VarDecl(VarDecl {
                name,
                value,
                ty,
                inferred_ty,
            }) => {
                write!(f, "let {}", name)?;
                if let Some(t) = inferred_ty {
                    write!(f, ": {} = ", t)?;
                } else if let Some(t) = ty {
                    write!(f, ": {} = ", t)?;
                } else {
                    write!(f, " = ")?;
                }
                value.pretty_print(f, spaces)
            }
            StmtKind::Expr(e) => e.pretty_print(f, spaces),
        }
    }
}

impl PrettyPrint for TypedStmtKind {
    fn pretty_print(&self, f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error> {
        match self {
            TypedStmtKind::VarDecl(TypedVarDecl { name, value }) => {
                write!(f, "let {}: {} = ", name, value.ty)?;
                value.pretty_print(f, spaces)
            }
            TypedStmtKind::Expr(e) => e.pretty_print(f, spaces),
        }
    }
}

impl PrettyPrint for Expr {
    fn pretty_print(&self, f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error> {
        self.node.pretty_print(f, spaces)
    }
}

impl PrettyPrint for Stmt {
    fn pretty_print(&self, f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error> {
        self.node.pretty_print(f, spaces)
    }
}

impl PrettyPrint for Decl {
    fn pretty_print(&self, f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error> {
        self.node.pretty_print(f, spaces)
    }
}

impl PrettyPrint for TypedDecl {
    fn pretty_print(&self, f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error> {
        self.node.pretty_print(f, spaces)
    }
}

impl PrettyPrint for TypedExpr {
    fn pretty_print(&self, f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error> {
        self.node.pretty_print(f, spaces)
    }
}

impl PrettyPrint for TypedStmt {
    fn pretty_print(&self, f: &mut Formatter<'_>, spaces: i32) -> Result<(), Error> {
        self.node.pretty_print(f, spaces)
    }
}

impl Decl {
    pub fn display_pretty(&self) -> PrettyPrintWrapper<'_, DeclKind> {
        PrettyPrintWrapper(&self.node)
    }
}

impl TypedDecl {
    pub fn display_pretty(&self) -> PrettyPrintWrapper<'_, TypedDeclKind> {
        PrettyPrintWrapper(&self.node)
    }
}
