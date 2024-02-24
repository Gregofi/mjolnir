use crate::frontend::types::Type;
use std::rc::Rc;

#[derive(Clone)]
pub struct WeaklyTypedIdentifier {
    pub name: String,
    pub ty: Option<String>,
}

#[derive(Clone)]
pub struct TypedIdentifier {
    pub name: String,
    pub ty: Rc<Type>,
}
