# Types

## Functions
When you use high order functions, you need a way to specify the type of the function. This is done by using the `(Params...) => ReturnType' syntax.

```scala
fn id(x: Int): Int => Int = (x) => x
```

When you have multiple parameters, you must use parentheses.

```scala
fn add(x: Int, y: Int): (Int, Int) => Int = (x, y) => x + y
```

