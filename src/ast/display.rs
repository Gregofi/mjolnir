use std::fmt::{Error, Formatter};

// TODO: Move Display impls to this guy
use crate::ast::*;

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

impl Display for TypedExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.node)
    }
}

impl Display for TypedDeclKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypedDeclKind::FunDecl {
                name,
                parameters,
                return_type,
                body,
            } => {
                write!(f, "fun {}(", name)?;
                let parameters = parameters
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{})", parameters)?;
                write!(f, ": {} {{\n{}\n}}", return_type, body)
            }
            TypedDeclKind::VarDecl(v) => {
                write!(f, "{}", v)
            }
            TypedDeclKind::StructDecl { name, fields } => {
                writeln!(f, "struct {} {{", name)?;
                let fields = fields
                    .iter()
                    .map(|f| f.to_string())
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}}}", fields)
            }
            TypedDeclKind::EnumDecl { name, variants } => {
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
