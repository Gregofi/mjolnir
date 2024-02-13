use std::collections::HashMap;

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
    fn is_same(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::BuiltIn(a), Type::BuiltIn(b)) => a == b,
            (
                Type::Struct {
                    fields: fields1,
                    methods: methods1,
                },
                Type::Struct {
                    fields: fields2,
                    methods: methods2,
                },
            ) => todo!(),
            (Type::Enum(fields1), Type::Enum(fields2)) => todo!(),
            (Type::FunctionType(f1), Type::FunctionType(f2)) => todo!(),
            _ => false,
        }
    }
}
