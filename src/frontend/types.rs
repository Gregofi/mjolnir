use std::{collections::HashMap, fmt::Display, rc::Rc};

use super::utils::GenericDeclaration;

type TypeIndex = String;

#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: String,
    pub ty: InstantiatedType,
}

#[derive(Debug, Clone)]
pub struct FunctionType {
    pub parameters: Vec<Parameter>,
    pub return_type: InstantiatedType,
}

pub struct Trait {
    pub methods: HashMap<String, FunctionType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuiltInType {
    Int,
    String,
    Bool,
    Char,
    Unit,
}

impl Display for BuiltInType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let as_str = match self {
            BuiltInType::Int => "Int",
            BuiltInType::String => "String",
            BuiltInType::Bool => "Bool",
            BuiltInType::Char => "Char",
            BuiltInType::Unit => "Unit",
        };
        f.write_str(as_str)
    }
}

#[derive(Debug, Clone)]
pub struct StructType {
    pub name: String,
    pub fields: HashMap<String, InstantiatedType>,
}

#[derive(Debug, Clone)]
pub struct EnumVariantType {
    pub name: String,
    pub fields: Vec<InstantiatedType>,
}

#[derive(Debug, Clone)]
pub struct EnumType {
    pub name: String,
    pub variants: Vec<EnumVariantType>,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    BuiltIn(BuiltInType),
    Struct(StructType),
    Enum(EnumType),
    Function(FunctionType),
}

/// Represents a type that is not bound to any AST node, and is "abstract". For example, a `Struct
/// Foo<T> { x: T }` would not be bound, it is a kind of scheme for types. The InstantiatedType
/// would be one bound to a specific TypeInfo, because it knows about instantiated generics.
#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub kind: TypeKind,
    pub generics: Vec<GenericDeclaration>,
}

/// Represents a type as it is written, for example `List[Option[T]]`.
#[derive(Debug, Clone)]
pub struct InstantiatedType {
    /// The name of the type, for example `Int` or `List`.
    /// Presumes that the types are stored in a
    /// HashMap<TypeIndex, TypeInfo>. This is used as a key to that hashmap.
    // TODO: Consider replacing this with Rc<TypeInfo>
    // If we do this, be careful that this is used
    // by the StructType and friends, and it represents
    // for example Struct x { foo: Option<T> }
    pub ty: TypeIndex,
    pub generics: Vec<InstantiatedType>,
}

impl InstantiatedType {
    pub fn get_primitive(name: &str) -> Self {
        InstantiatedType {
            ty: name.to_string(),
            generics: vec![],
        }
    }
}

impl Display for InstantiatedType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let generics = if self.generics.is_empty() {
            "".to_string()
        } else {
            format!(
                "<{}>",
                self.generics
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            )
        };
        write!(f, "{}{}", self.ty, generics)
    }
}

impl TypeKind {
    pub fn is_same(&self, other: &Self) -> bool {
        match (self, other) {
            (TypeKind::BuiltIn(a), TypeKind::BuiltIn(b)) => a == b,
            (TypeKind::Function(_), TypeKind::Function(_)) => todo!(),
            (TypeKind::Struct(s1), TypeKind::Struct(s2)) => s1.name == s2.name,
            (TypeKind::Enum(e1), TypeKind::Enum(e2)) => e1.name == e2.name,
            _ => false,
        }
    }

    pub fn is_bool(&self) -> bool {
        matches!(self, TypeKind::BuiltIn(BuiltInType::Bool))
    }

    #[allow(dead_code)]
    pub fn is_int(&self) -> bool {
        matches!(self, TypeKind::BuiltIn(BuiltInType::Int))
    }

    pub fn get_bool() -> Rc<TypeKind> {
        TypeKind::BuiltIn(BuiltInType::Bool).into()
    }

    pub fn get_int() -> Rc<TypeKind> {
        TypeKind::BuiltIn(BuiltInType::Int).into()
    }

    pub fn get_unit() -> Rc<TypeKind> {
        TypeKind::BuiltIn(BuiltInType::Unit).into()
    }

    pub fn get_char() -> Rc<TypeKind> {
        TypeKind::BuiltIn(BuiltInType::Char).into()
    }

    pub fn as_function(&self) -> Option<&FunctionType> {
        match self {
            TypeKind::Function(f) => Some(f),
            _ => None,
        }
    }
}

impl Display for TypeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let as_str = match self {
            TypeKind::BuiltIn(b) => b.to_string(),
            TypeKind::Struct(StructType { name, fields }) => {
                let fields_str = fields
                    .iter()
                    .map(|(name, ty)| format!("{}: {}", name, ty))
                    .collect::<Vec<String>>()
                    .join(", ");
                format!("struct {} {{{}}}", name, fields_str)
            }
            TypeKind::Enum(EnumType { name, variants }) => {
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
            TypeKind::Function(_) => "Function".to_string(),
        };
        f.write_str(&as_str)
    }
}
