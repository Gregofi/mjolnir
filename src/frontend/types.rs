use crate::frontend::utils::TypedIdentifier;
use std::{collections::HashMap, fmt::Display, rc::Rc};

type IndirectType = String;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    pub name: String,
    pub ty: IndirectType,
}

#[derive(Debug, Clone)]
pub struct FunctionType {
    pub parameters: Vec<Parameter>,
    pub return_type: IndirectType,
}

impl FunctionType {
    pub fn wrap(&self) -> Rc<Type> {
        Type::FunctionType(Box::new(self.clone())).into()
    }
}

pub struct Trait {
    pub methods: HashMap<String, FunctionType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuiltInType {
    Int,
    String,
    Bool,
    Unit,
}

impl Display for BuiltInType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let as_str = match self {
            BuiltInType::Int => "Int",
            BuiltInType::String => "String",
            BuiltInType::Bool => "Bool",
            BuiltInType::Unit => "Unit",
        };
        f.write_str(as_str)
    }
}

#[derive(Debug, Clone)]
pub struct StructType {
    pub name: String,
    pub fields: HashMap<String, IndirectType>,
}

#[derive(Debug, Clone)]
pub struct EnumVariantType {
    pub name: String,
    pub fields: Vec<IndirectType>,
}

#[derive(Debug, Clone)]
pub struct EnumType {
    pub name: String,
    pub variants: Vec<EnumVariantType>,
}

#[derive(Debug, Clone)]
pub enum Type {
    BuiltIn(BuiltInType),
    Struct(StructType),
    Enum(EnumType),
    FunctionType(Box<FunctionType>),
}

impl Type {
    pub fn is_same(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::BuiltIn(a), Type::BuiltIn(b)) => a == b,
            (Type::FunctionType(f1), Type::FunctionType(f2)) => todo!(),
            (Type::Struct(s1), Type::Struct(s2)) => s1.name == s2.name,
            (Type::Enum(e1), Type::Enum(e2)) => e1.name == e2.name,
            _ => false,
        }
    }

    pub fn is_bool(&self) -> bool {
        match self {
            Type::BuiltIn(BuiltInType::Bool) => true,
            _ => false,
        }
    }

    #[allow(dead_code)]
    pub fn is_int(&self) -> bool {
        match self {
            Type::BuiltIn(BuiltInType::Int) => true,
            _ => false,
        }
    }

    pub fn get_bool() -> Rc<Type> {
        Type::BuiltIn(BuiltInType::Bool).into()
    }

    pub fn get_int() -> Rc<Type> {
        Type::BuiltIn(BuiltInType::Int).into()
    }

    pub fn get_unit() -> Rc<Type> {
        Type::BuiltIn(BuiltInType::Unit).into()
    }

    pub fn as_function(&self) -> Option<&FunctionType> {
        match self {
            Type::FunctionType(f) => Some(f),
            _ => None,
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let as_str = match self {
            Type::BuiltIn(b) => b.to_string(),
            Type::Struct(StructType { name, fields }) => {
                let fields_str = fields
                    .iter()
                    .map(|(name, ty)| format!("{}: {}", name, ty))
                    .collect::<Vec<String>>()
                    .join(", ");
                format!("struct {} {{{}}}", name, fields_str)
            }
            Type::Enum(EnumType { name, variants }) => {
                let variants_str = variants
                    .iter()
                    .map(|v| {
                        let fields_str = v
                            .fields
                            .iter()
                            .map(|ty| ty.to_string())
                            .collect::<Vec<String>>()
                            .join(", ");
                        format!("{}({})", v.name, fields_str)
                    })
                    .collect::<Vec<String>>()
                    .join(", ");
                format!("enum {} {{{}}}", name, variants_str)
            }
            Type::FunctionType(_) => "Function".to_string(),
        };
        f.write_str(&as_str)
    }
}
