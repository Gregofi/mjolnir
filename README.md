# Mjolnir

## Introduction

Mjolnir is a statically typed functional programming language with a focus on simplicity and minimalism.
It aims to have a simplicity of Go, syntax of Rust and semantics of Lisp.
Resulting in a very tiny language, which can be used to learn functional basic concepts like algebraic data types (ADT), pattern matching, immutability and so on.
The language has a syntax that should be familiar to anyone who has used a C-like language.
Currently, the language is very close to Rust in terms of syntax.

The language is still in its very early stages.
The interpreter is not optimized and is used to quickly prototype the language.

## Installation

To install Mjolnir, use the provided script, which also installs the standard library

```sh
TODO
```

## Language Tutorial

This tutorial shows the basics features of Mjolnir, as well as teaching some basics of functional programming.
We assume that the reader is familiar with some programming language, but not with functional programming.

We will show how to write a simple program that reads numbers from user, sorts them and prints them back.

Every Mjolnir program starts with a `main` function, which is the entry point of the program.

```rust
fn main(): Int = {
    0
}
```

This is the simplest program you can write in Mjolnir, it quits with exit code zero.
Mjolnir is expression driven, almost everything is an expression,
it does not have `return` statement.
The last expression in the compount expression is returned.
In fact, the function body is one expression, which is a compound expression in the example.
Compound expression can have multiple statement and one expression at the end, which is the resulting value.
For example, this is perfectly legal:

```rust
fn foo(): Int = {
    { 1 + 2 } + { 3 }
}

// Or, you dont have to use compound expression

fn bar(): Int = 5 + 5
```


The `Int` type is the return type of the function.
The `main` function is special, it must return an integer, which is the exit code of the program.

We will leave the input/output part for later, and focus on sorting the numbers.
Mjolnir has some containers in its standard library, but for the sake of learning the language, we will implement our own container.
We have these types to work with:

- `Int` - integer type
- `Bool` - boolean type
- `Char` - UTF8 character

We also have product types, called `struct`. These work like structs from C, Rust, Go and so on. They are used to group multiple values into one.

```rust
struct Pair {
    first: Int,
    second: Int,
}

fn main(): Int = {
    let x = 1;
    let y = 2;
    let pair = &Pair { first: x, second: y };
    pair.first + pair.second
}
```

Do note that all values are immutable, you can't change the value of any variable nor struct members after it is assigned.

Struct type will definitely be handy, however, we need a container to store multiple values.
This can be implemented via sum type.
They are also a combination of multiple values, but they are disjoint, meaning that only one value can be present at a time (contrary to product types, where all values are present).

They are less common in imperative programming languages:
- `std::variant` in C++
- `enum` in Rust

Other languages use some sort of structure with a tag:

```typescript
type AlertType = "email" | "sms";

interface EmailAlert {
    type: "email";
    subject: string;
    message: string;
}

interface SmsAlert {
    type: "sms";
    number: string;
    message: string;
}

interface Alert {
    type: AlertType;
    alert: EmailAlert | SmsAlert;
}

function sendAlert(alert: Alert) {
    if (alert.type === "email") {
        let email = alert.alert as EmailAlert;
        // some logic to send email
    } else {
        let sms = alert.alert as SmsAlert;
        // some entirely different logic to send sms
    }
}
```

A short illustrative example in typescript.
Here, an `Alert` can be either an `EmailAlert` or an `SmsAlert`, but not both at the same time.
Mjolnir has a similar construct, called `enum`.

We will try to implement a simple container structure.

```rust
enum List {
    Cons(Int, List),
    Nil,
}
```

This is a simple linked list, which can store integers.
The `Cons` variant has two fields, the first is an integer, and the second is a `List`.
The `Nil` variant is an empty list.

We can construct the list like so:

```rust
fn main(): Int = {
    // A linked list [1, 2, 3]
    let list = Cons(1, Cons(2, Cons(3, Nil())));
    0
}
```

The list is semantically either a pair of an integer and a list, or an empty list.
For implementing functions, it is way easier to think about it as a pair of an integer and a list,
not as a number and reference to the next element.

We have the list instantiated, but currently have no way to work with it.
For this, we can use pattern matching:

```rust
fn main(): Int = {
    let list = Cons(1, Cons(2, Cons(3, Nil())));
    match list {
        Cons(head, tail) => head,
        Nil => 0,
    }
}
```

Pattern matching allows to decompose and match the structure of the value.
It allows to decide based on the type of the value, and extract the values from it.

Let us do something more interesting.
If you wanted to sum all elements in the list, you would probably think about a cycle and a sum variable.
However, Mjolnir has all variables immutable, so we can't change the sum variable.

Lets presume that we a friend that implemented `_sum` function for us.
This function can sum all elements in the list.
However, it can only sum the list that is one element shorter than the current list.
This means, if we have a list `[1, 2, 3]`, we can a `[2, 3]` to the function.
Having this magical function, we could implement it like so:

```rust
fn sum(list: List): Int = match list {
    Cons(head, tail) => head + _sum(tail),
    Nil => 0,
}
```

We let our friend `_sum` calculate the rest of the list, and just add to it what we hold in our hand, the `1` from `[1, 2, 3]`.
Also, someone may pass us an empty list, so we need to handle that case as well.

And now, we can just swap `_sum` with `sum` in our `main` function, and it will all work.
Mjolnir also has methods, so we could implement the `sum` function as a method of the `List` type.

```rust
List {
    Cons(head, tail),
    Nil,
}

impl List {
    fn sum(): Int = match self {
        Cons(head, tail) => head + tail.sum(),
        Nil => 0,
    }
}
```

and thats it!
This is a way that you should think about recursive functions.
The way we do it, we calculate the sum of the rest of the list (and we shouldn't think too hard about how that happens), take it and add to it the head which we currently hold.
Also, always remember to handle the base case, which is the empty list in this case.

Another similar example is the `push` function.

```rust
impl List {
    fn push(n: Int): List = match self {
        Cons(head, tail) => Cons(head, tail.append(n)),
        Nil => Cons(n, Nil()),
    }
}
```

This function takes a number and adds it to the end of the list.
If the list is empty, it creates a new list with the number.
See that you have to use parentheses to call the constructor, because the `Nil` is a function that returns a `List`, it is not special in any way.

Another interesting function is the `reverse` function.
Here, we have to use a little trick.
In our previous recursive functions, we always calculated the result of the rest of the list, and then added the head to it.
This means that the first call of the `+` or `Cons` function is on the last element of the list.
```
1 + sum([2, 3]) ->
1 + (2 + sum([3])) ->
1 + (2 + (3 + sum([]))) ->
1 + (2 + (3 + 0)) ->
1 + (2 + 3) ->
1 + 5 ->
6
```

If we just did
```rust
impl List {
    fn reverse(): List = match self {
        Cons(head, tail) => Cons(head, tail.reverse()),
        Nil => Nil(),
    }
}
```
we would implement identity function.
We need to perform the first `Cons` call on the first element of the list and the neutral element (empty list) as the second argument.

```
reverse([], [1, 2, 3]) :: reverse(Cons(1, []), [2,3]) ->
reverse([1], [2, 3]) ->
reverse([2, 1], [3]) ->
reverse([3, 2, 1], []) ->
[3, 2, 1]
```


```rust
impl List {
    fn reverse(): List = _reverse(Nil())
    
    fn _reverse(acc: List): List = match self {
        Cons(head, tail) => tail._reverse(Cons(head, acc)),
        Nil => acc,
    }
}
```

This is a common pattern in functional programming, where you have to use an accumulator to store the result of the computation.
The accumulator is passed to the next call, and the result is calculated based on it.

We can generalize both of these functions into a `fold_left` and `fold_right` functions.
For example, to generalize the `sum` function, we can create a function like this
```rust
fn fold_right[U](f: (Int, U) => U, init: Int): U = match self {
    Cons(head, tail) => f(head, tail.fold_right(f)),
    Nil => f(0, Nil()),
}
```

Notice the generic type parameter, where any type can be passed to the function.
Also, the function `f` is passed as an argument, and it is a function that takes an integer (the type of the members of the list) and the accumulator and returns the accumulator.
Now, to sum all elements in the list, we can just call `fold_right` with the `+` function and the neutral element `0`.

```
list.fold_right(|a, b| { a + b }, 0)
```

Fold left is similar, but passes the result into accumulator.

```rust
impl List {
    fn fold_left[U](f: (Int, U) => U, init: U): U = match self {
        Cons(head, tail) => tail.fold_left(f, f(head, init)),
        Nil => init,
    }

    fn fold_right[U](f: (Int, U) => U, init: U): U = match self {
        Cons(head, tail) => f(head, tail.fold_right(f, init)),
        Nil => init,
    }
}
```

With fold left, we can implement the `reverse` function like so:

```rust
impl List {
    fn reverse(): List = self.fold_left(|a, b| { Cons(a, b) }, Nil())
}
```

Or even simpler

```rust
impl List {
    fn reverse(): List = self.fold_left(Cons, Nil())
}
```

Since `Cons` is a function like any other, we can pass it as an argument.
Try to come up with a `map` and `filter` functions for the list using the fold functions!











