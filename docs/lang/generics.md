# Generics

Mjolnir supports generic members and generic parameters.
The syntax for enums is following:
```mjolnir
enum List[T] {
    Cons(T, List[T]),
    Nil
}

fn main() = match Cons(1, Nil()) { ... }
```

The syntax for functions is following:
```mjolnir
fn foo[T](x: T): List[T] = Cons(x, Nil()) 
```

As of 0.1, the language does not allow to narrow the type of a generic parameter.
This means that generics are mainly used to implement collections, which only store the type but otherwise do not care about it.
For functions, they allow to pass enums and structs with generic parameter.
But they do not allow to implement a function that works for any type that implements a certain trait.
