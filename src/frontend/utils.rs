use std::collections::HashMap;
use std::fmt::Display;

use super::types::InstantiatedType;

#[derive(Clone, Debug)]
pub struct GenericDeclaration {
    pub name: String,
    // pub bounds: Vec<Type>,
}

impl Display for GenericDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// This is not the same as instantiated type. For example,
/// this is    fn foo[T](x: Option[T]): T where T impls Stringable = { ... }
/// TypeDeclaration-> ^     ^^^^^^^^^ <- InstantiatedType
#[derive(Clone, Debug)]
pub struct TypeDeclaration {
    pub name: String,
    pub generics: Vec<GenericDeclaration>,
}

impl Display for TypeDeclaration {
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
        write!(f, "{}{}", self.name, generics)
    }
}

/// The type that was "written" in the source code directly, without any semantic information.
#[derive(Clone, Debug)]
pub enum WrittenType {
    /// Name of the type + its generics (Person[T, U]), Int...
    Identifier {
        name: String,
        generics: Vec<WrittenType>,
    },
    /// Function type Int => Int; (List[T], T) => List[T]
    Function {
        params: Vec<WrittenType>,
        return_type: Box<WrittenType>,
    },
}

impl Display for WrittenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WrittenType::Identifier { name, generics } => {
                let generics = if generics.is_empty() {
                    "".to_string()
                } else {
                    format!(
                        "<{}>",
                        generics
                            .iter()
                            .map(|g| g.to_string())
                            .collect::<Vec<String>>()
                            .join(", ")
                    )
                };
                write!(f, "{}{}", name, generics)
            }
            WrittenType::Function {
                params,
                return_type,
            } => {
                let params = if params.is_empty() {
                    "".to_string()
                } else if params.len() == 1 {
                    params[0].to_string()
                } else {
                    format!(
                        "({})",
                        params
                            .iter()
                            .map(|p| p.to_string())
                            .collect::<Vec<String>>()
                            .join(", ")
                    )
                };
                write!(f, "{} => {}", params, return_type)
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct WeaklyTypedIdentifier {
    pub name: String,
    pub ty: Option<WrittenType>,
}

#[derive(Clone, Debug)]
pub struct StronglyTypedIdentifier {
    pub name: String,
    pub ty: WrittenType,
}

#[derive(Clone, Debug)]
pub struct TypedIdentifier {
    pub name: String,
    pub ty: InstantiatedType,
}

impl Display for WeaklyTypedIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.ty {
            Some(ty) => write!(f, "{}: {}", self.name, ty),
            None => write!(f, "{}", self.name),
        }
    }
}

impl Display for StronglyTypedIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.ty)
    }
}

impl Display for TypedIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.ty)
    }
}

pub struct IdEnv<T> {
    ids: Vec<HashMap<String, T>>,
}

impl<T> IdEnv<T> {
    pub fn new() -> IdEnv<T> {
        IdEnv {
            ids: vec![HashMap::new()],
        }
    }

    pub fn push(&mut self) {
        self.ids.push(HashMap::new());
    }

    pub fn pop(&mut self) {
        self.ids.pop().expect("No environment present");
    }

    pub fn insert(&mut self, key: String, value: T) {
        self.ids
            .last_mut()
            .expect("No environment present")
            .insert(key, value);
    }

    pub fn get(&self, key: &String) -> Option<&T> {
        for env in self.ids.iter().rev() {
            if let Some(value) = env.get(key) {
                return Some(value);
            }
        }
        None
    }
}
