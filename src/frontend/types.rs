pub enum Type {
    Int,
    Bool,
    String,
    Product(Vec<(String, Type)>),
    Sum(Vec<(String, Type)>),
}
