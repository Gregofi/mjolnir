use std::collections::HashMap;

pub struct Environment<T> {
    symbols: HashMap<String, T>,
}

impl<T> Environment<T> {
    fn new() -> Self {
        Self {
            symbols: HashMap::new(),
        }
    }
}

pub struct SymbolTable<T> {
    pub identifiers: Vec<Environment<T>>,
}

impl<T> SymbolTable<T> {
    pub fn new() -> Self {
        Self {
            identifiers: Vec::new(),
        }
    }

    pub fn push(&mut self) {
        self.identifiers.push(Environment::new());
    }

    pub fn pop(&mut self) {
        self.identifiers.pop();
    }

    pub fn insert(&mut self, name: String, value: T) {
        self.identifiers.last_mut().unwrap().symbols.insert(name, value);
    }

    pub fn get(&self, name: &str) -> Option<&T> {
        self.identifiers.iter().rev().find_map(|env| env.symbols.get(name))
    }
}
