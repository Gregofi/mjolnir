use crate::frontend::types::Type;
use std::rc::Rc;

#[derive(Clone)]
pub struct WeaklyTypedIdentifier {
    pub name: String,
    pub ty: Option<String>,
}

#[derive(Clone, Debug)]
pub struct StronglyTypedIdentifier {
    pub name: String,
    pub ty: String,
}

#[derive(Clone, Debug)]
pub struct TypedIdentifier {
    pub name: String,
    pub ty: Rc<Type>,
}
