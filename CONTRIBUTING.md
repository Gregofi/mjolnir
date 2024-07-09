# Mjolnir

Mjolnir is a _functional_ programming language.
It aims to have a simplicity of Go, syntax of Rust and semantics of Lisp.
Therefore, the language is minimal, statically typed and functional.
It uses algebraic data types (ADT) and pattern matching as its building blocks.

An example of a simple program in Mjolnir, which implements a linked list:

```mjolnir
enum List[T] {
    Cons(T, List[T]),
    Nil
}

impl List[T] {
    fn fold_left[U](f: (T, U): U, acc: U): U = {
        match self {
            Cons(head, tail) => tail.fold_left(f, f(head, acc)),
            Nil => acc
        }
    }

    fn reverse(): List[T] = self.fold_left(Cons, Nil())
}

fn main(): Int = {
    let list = Cons(1, Cons(2, Cons(3, Nil())));
    let reversed = list.reverse();
    0
}

```

The standard library `List` container is implemented in the same way, using ADT.
You can find the whole language specification at the bottom of this README.

# Installation

To install Mjolnir, you need to have `cargo` installed.
Then, you can run the following command:

```sh
cargo install --path .
```

This will install the `mjolnir` binary in your `~/.cargo/bin` directory.

# Usage

To run a Mjolnir program, you can use the following command:

```sh
mjolnir interpret <file.mj>
```

# Development

To run the tests, you can use the following command:

```sh
cargo test
```

There are also standard library test (`/stdlib_tests`), run these with:

```sh
./test_stdlib.sh
```

from the project root directory.

# Language Specification

The top-level structure of a Mjolnir program is a list of declarations.

## Types

Mjolnir has the following built-in types:

- `Int`: 64-bit signed integer
- `Bool`: boolean
- `Char`: Unicode character

From these, you can build more complex types using enums and structs, as described below.

## Declarations

### Function Declaration


A function declaration consists of a function name, a list of parameters and a return type.
The body of the function is an expression.

```mjolnir
fn add(a: Int, b: Int): Int = a + b

fn add(a: Int, b: Int): Int = { a + b }
```

The `{ ... }` is also an expression, which evaluates to the last expression in the block.

These functions must always be explicitly typed.
Functions might also have type parameters.
These cannot be narrowed, as traits are not yet implemented.

```mjolnir
fn id[T](a: T): T = a
```

### Enum Declaration

An enum represent the sum type.
Its declaration consists of a name and a list of variants.
Each variant can have a list of types.

```mjolnir
enum Option[T] {
    Some(T),
    None,
}
```

### Struct Declaration

A struct represent the product type.
Its declaration consists of a name and a list of fields.
Each field has a name and a type.

```mjolnir
struct Point {
    x: Int,
    y: Int,
}
```

### Impl Declaration

An impl declaration associates a functions (methods) with a type.
The type can be a struct or an enum.

```mjolnir
impl Point {
    fn new(x: Int, y: Int): Point = Point { x, y }
}

impl Option[T] {
    fn is_some(): Bool = {
        match self {
            Some(_) => true,
            None => false,
        }
    }
}
```

## Expressions

A body of a function is an expression.
An expression can be a literal, a variable, a function call, a block, a match expression, a let binding or a return statement.

### Literal

A literal is a constant value, either an integer, a character or a boolean.

### Variable

A variable is a name that refers to a value.

```mjolnir
let x = 42;
```

Variables are immutable, once declared, they can never be changed.

### Function Call

A function call is an expression that calls a function with a list of arguments.

```mjolnir
add(1, 2)
```

