use std::{collections::HashMap, fmt::Display};

pub struct FunctionType {
    parameters: Vec<Type>,
    return_type: Type,
}

pub struct StructType {
    fields: HashMap<String, Type>,
    methods: HashMap<String, FunctionType>,
    implemented_traits: Vec<String>,
}

pub struct Trait {
    methods: HashMap<String, FunctionType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuiltInType {
    Int,
    String,
    Bool,
}

impl Display for BuiltInType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let as_str = match self {
            BuiltInType::Int => "Int",
            BuiltInType::String => "String",
            BuiltInType::Bool => "Bool",
        };
        f.write_str(as_str)
    }
}

pub enum Type {
    BuiltIn(BuiltInType),
    Struct {
        fields: HashMap<String, Type>,
        methods: HashMap<String, FunctionType>,
    },
    Enum(Vec<(String, Type)>),
    FunctionType(Box<FunctionType>),
}

impl Type {
    pub fn is_same(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::BuiltIn(a), Type::BuiltIn(b)) => a == b,
            (
                Type::Struct {
                    fields: f1,
                    methods: m1,
                },
                Type::Struct {
                    fields: f2,
                    methods: m2,
                },
            ) => todo!(),
            (Type::Enum(fields1), Type::Enum(fields2)) => todo!(),
            (Type::FunctionType(f1), Type::FunctionType(f2)) => todo!(),
            _ => false,
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let as_str = match self {
            Type::BuiltIn(b) => b.to_string(),
            Type::Struct { .. } => "Struct".to_string(),
            Type::Enum(_) => "Enum".to_string(),
            Type::FunctionType(_) => "Function".to_string(),
        };
        f.write_str(&as_str)
    }
}
