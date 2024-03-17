# AST Interpreter

The AST interpreter is a very basic, no optimizations interpreter used to quickly prototype the language.

The interpreter expects the AST to be fully typed, and it will not perform any type checking.
The interpreter makes no guarantees about what will happen if the AST is not fully typed (the program may panic).
