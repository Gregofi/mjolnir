use std::rc::Rc;
use crate::frontend::types::Type;



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
