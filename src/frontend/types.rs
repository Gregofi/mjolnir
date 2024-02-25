use crate::frontend::utils::TypedIdentifier;
use std::{collections::HashMap, fmt::Display, rc::Rc};

#[derive(Debug, Clone)]
pub struct FunctionType {
    pub parameters: Vec<TypedIdentifier>,
    pub return_type: Rc<Type>,
}

impl FunctionType {
    pub fn check_args(&self, args: &[Rc<Type>]) -> bool {
        if self.parameters.len() != args.len() {
            return false;
        }
        self.parameters
            .iter()
            .zip(args)
            .all(|(expected, actual)| expected.ty.is_same(actual))
    }

    pub fn wrap(&self) -> Rc<Type> {
        Type::FunctionType(Box::new(self.clone())).into()
    }
}

pub struct StructType {
    pub fields: HashMap<String, Rc<Type>>,
    pub methods: HashMap<String, FunctionType>,
    pub implemented_traits: Vec<String>,
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

    pub fn is_bool(&self) -> bool {
        match self {
            Type::BuiltIn(BuiltInType::Bool) => true,
            _ => false,
        }
    }

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
            Type::Struct { .. } => "Struct".to_string(),
            Type::Enum(_) => "Enum".to_string(),
            Type::FunctionType(_) => "Function".to_string(),
        };
        f.write_str(&as_str)
    }
}
