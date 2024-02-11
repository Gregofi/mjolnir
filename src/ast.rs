pub struct Location {
    pub line: usize,
    pub column: usize,
}

impl Location {
    pub fn new(line: usize, column: usize) -> Location {
        Location {
            line,
            column,
        }
    }
}

pub struct Expr {
    pub node: ExprKind,
    pub location: Location,
}

pub enum ExprKind {
    Int(i64),
    Identifier(String),
}

pub struct Stmt {
    pub node: StmtKind,
    pub location: Location,
}

pub struct TypedIdentifier {
    pub name: String,
    pub ty: Option<String>,
}

pub enum StmtKind {
    FunDecl{name: String, parameters: Vec<TypedIdentifier>, return_type: Option<String>, body: Box<Expr>},
    StructDecl{name: String, fields: Vec<TypedIdentifier>},
    // We allow writing variants similar to structs.
    EnumDecl{name: String, variants: Vec<TypedIdentifier>},
    TraitDecl{name: String, methods: Vec<TypedIdentifier>},
    Top(Vec<Stmt>),
}
