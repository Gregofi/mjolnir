use std::fmt::{Error, Formatter};

// TODO: Move Display impls to this guy
use crate::ast::*;

impl Display for FunDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let FunDecl {
            name,
            generics,
            parameters,
            return_type,
            body,
            inferred_parameters,
            inferred_return_type,
        } = self;
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
}

impl Display for Decl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.node {
            DeclKind::FunDecl(fun) => {
                write!(f, "{}", fun)
            }
            DeclKind::StructDecl {
                name,
                generics,
                fields,
                ..
            } => {
                write!(f, "struct {}", name)?;

                if !generics.is_empty() {
                    write!(f, "[")?;
                    let generics: Vec<String> = generics.iter().map(|x| x.to_string()).collect();
                    write!(f, "{}", generics.join(", "))?;
                    write!(f, "]")?;
                }

                write!(f, " {{")?;
                let fields = fields
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}", fields)?;
                write!(f, "}}")
            }
            DeclKind::ImplDecl {
                target,
                generics,
                methods,
            } => {
                write!(f, "impl {}", target)?;

                if !generics.is_empty() {
                    write!(f, "[")?;
                    let generics: Vec<String> = generics.iter().map(|x| x.to_string()).collect();
                    write!(f, "{}", generics.join(", "))?;
                    write!(f, "]")?;
                }

                write!(f, " {{")?;
                for method in methods {
                    write!(f, "{}", method)?;
                }
                write!(f, "}}")
            }
            DeclKind::EnumDecl {
                name,
                variants,
                generics,
                ..
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

impl<A, B, LambdaFun> Display for ExprKind<A, B, LambdaFun>
where
    A: Display,
    B: Display,
    LambdaFun: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprKind::Unit => write!(f, "()"),
            ExprKind::Int(x) => write!(f, "{}", x),
            ExprKind::Boolean(x) => write!(f, "{}", x),
            ExprKind::Char(x) => write!(f, "{}", x),
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
            ExprKind::Lambda(fun) => {
                write!(f, "{}", fun)
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

impl Display for EnumVariant {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "{}", self.name)?;
        let fields = self
            .fields
            .iter()
            .map(|f| f.to_string())
            .collect::<Vec<String>>()
            .join(", ");
        write!(f, "({})", fields)
    }
}

impl Display for TypedVarDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.name, self.value)
    }
}

impl Display for TypedStmtKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypedStmtKind::VarDecl(tvd) => {
                write!(f, "{}", tvd)
            }
            TypedStmtKind::Expr(e) => {
                write!(f, "{}", e)
            }
        }
    }
}

impl Display for TypedStmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.node)
    }
}

impl Display for TypedFunDecl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "fun {}(", self.name)?;
        let parameters = self
            .parameters
            .iter()
            .map(|p| p.to_string())
            .collect::<Vec<String>>()
            .join(", ");
        write!(f, "{})", parameters)?;
        write!(f, ": {} {{\n{}\n}}", self.return_type, self.body)
    }
}

impl Display for TypedExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.node)
    }
}

impl Display for TypedDeclKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypedDeclKind::FunDecl(fun) => {
                write!(f, "{}", fun)
            }
            TypedDeclKind::VarDecl(v) => {
                write!(f, "{}", v)
            }
            TypedDeclKind::StructDecl { name, fields, .. } => {
                writeln!(f, "struct {} {{", name)?;
                let fields = fields
                    .iter()
                    .map(|f| f.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}}}", fields)
            }
            TypedDeclKind::EnumDecl { name, variants, .. } => {
                writeln!(f, "enum {} {{", name)?;
                let variants = variants
                    .iter()
                    .map(|v| v.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}}}", variants)
            }
            TypedDeclKind::VariantConstructor { name, fields_count } => {
                write!(f, "{}(arity: {})", name, fields_count)
            }
        }
    }
}
