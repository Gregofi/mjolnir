# Types

Types are inferred via MH type inference.
They can also be specified explicitly.

The types `T` are represented by two values:
- Type variables (`t_1`, ...), these are not a concrete type, rather it is a placeholder for a type.
- Constructors, represented by a name, and a list of types `T`.
For example `Int`, `Bool`, `List[Int]`, List[Option[Either[Int, t_1]]]` and so on.
Functions are represented as a constructor where the first type is the return type, and the rest are the parameters.
For example `(A, B) => C` would be `Function[C, A, B]`. 

At the end of type inference, the type variables should not be present anywhere in the types.

The types are also sometimes wrapped in a `TypeScheme` object.
This represents a type that hasn't instantiated generics.
For example, the
```
fn foo[A](a: A) -> A {
    a
}
```
would be a typescheme of `Constructor{ name: "foo", types: ["A"] }`, with generics ["A"].
When this type is used somewhere, the generics are replaced with the actual types (which are either type variables or constructors).
