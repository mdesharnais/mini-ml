# Mini ML

This is a compiler for a subset of ML developped as part of a *Praktikum* in
compiler construction at the LMU.

## Project goal

Goal: Compile the following OCaml-fragment to machine code using LLVM

    t ::=
        | i                   (integer constant)
        | true                (boolean true constant)
        | false               (boolean false constant)
        | t op t              (op from =, <, +, -, *, /)
        | fun x -> t          (function abstraction)
        | t t                 (function application)
        | if t then t else t  (conditional branching)
        | let x = t in t      (variable binding)
        | let rec f = t in t  (recursive function binding)
        | extern x            (external function reference)
        | (t)                 (expression grouping)

## Operator precedence

The precedence is as followed, where operators seen first have precedence over
those seen after.

 - Function composition
 - Multiplication `*`, division `/`
 - Addition `+`, subtraction `-`
 - Comparison `<`, equality `=`
 - Branching `if then else`, `let` and `let rec` binding
 - Function abstraction `fun ->`

## External functions

The expression `extern f` behave like a variable of type `int -> int`, except
that it calls an externally defined function. As an example the function `print`
is defined in `src/libutil.c`, which is automatically linked, and print its
64-bits integer argument to stdout. It can be use as follow:

    extern print (1 + 1)

## Type system

The type system implements let-polymorphism. All free type variables are
universally quantified when binded with the `let` or `let rec` construct,
resulting in a type schema. The typing context is an mapping from variables to
type schemas. These are instanciated when every time a variable is referenced.

    type-schema ::=
        | forall x. type     (universal quantification)
        | type               (underlying type)

    type ::=
        | int                (64 bits integer)
        | bool               (boolean)
        | t -> t             (function)
        | α                  (type variables)

## Closure implementation

A closure is implemented as a 2-fields struct. The first field contains the 64
bits function pointer. The second field is an array of environment variables.
Those are encoded as 64 bits integers, which must be cast when inserted and
extracted.

```
0              64             128            192            (n + 1) * 64
+--------------+--------------+--------------+--------------+
| Fun. pointer | Env. var. 1  | Env. var. 2  | Env. var. n  |
+--------------+--------------+--------------+--------------+
```

## Garbage collection

The default memory allocation strategy uses a simple `malloc(3)` and never
deallocate memory. An alternative implementation uses the [Boehm-Demers-Weiser
conservative C/C++ Garbage Collector](https://www.hboehm.info/gc/).

## Optimizations

### Constant propagation

There is a very trivial constant propagation which optimizes unnecessarily
trivial `let`-bindings. e.g. in the folloging, `n` gets inline at every use.

    let n = 10 in ...

### Closure avoidance

A static analysis is performed to detect when a closure is not necessary. In
that case, a normal function is generated.

## To do

 - Lexer (alex)
 - Parser (happy)
   - concrete grammar
     - Precedence rules for arithmetic operators
       http://caml.inria.fr/pub/docs/manual-ocaml/expr.html
     - t1 t2 t3 should be parsed as (t1 t2) t3
   - implementent parser using parser generator
   - error messages
 - abstract syntax tree
   - generation of abstract syntax by parser actions
   - printing of parsed program
 - interpreter

## Build the project

To build the project:

    $ stack build

To execute the compiled binary:

    $ stack exec mini-ml-exe examples/prog1.miniml

To run the tests:

    $ stack test

## Example programs

The directory `examples` contains a few programs which can be compiled and
executed using the script `./compile examples`. In a normal run, only the name
of the programm is displayed. However, in the event of a compilation or
execution error, the output will be displayed on stdout.

## Possible extensions

### Type annotation

Even though the types are fully infered, it would be usefull in many contexts,
to be able to write type annotations directly in the source code. The folllowing
syntax additions would be welcome:

    let x : type-schema = e1 in e2
    let rec f : type-schema = fun x -> e1 in e2
    let rec f : type-schema = fun (x : type) -> e1 in e2
    fun (x : type) -> e
    (e : type)

### Generalized external function

External functions are currently limitted to have type `int -> int`. With the
addition of n-tuples, it would be possible to refer to any exterally defined
function. The syntax needs to be change as followed:

    extern (f : type)

e.g.

    extern (max : int * int -> int)

### Polymorphic function code generation

Currently, code is only generated for non-polymorphic functions. A strategy must
be chosen: either one generic function or many specialized one (à la C++
template).

Literature on the subject?

## Test infrastructure

The current `test/Spec.hs` test infracstructure is highly unsatisfactory. It is
hard to read, hard to extend and hard to modify. It requires extensive
modification every time the intermediate language or the type inference
implementation change.

The `examples` directory is an improvement, but only tests if compilation and
executioin succeed, not if the types and results are correct.

The former would be possible with type annotations, while the later could be
implemented with special comments in the source code, asserting the result of
some implementation functions.

## References

 - https://www.tcs.ifi.lmu.de/lehre/ws-2014-15/compilerbau/material/straightline.zip
 - https://www.tcs.ifi.lmu.de/lehre/ws-2014-15/compilerbau
 - http://caml.inria.fr/pub/docs/u3-ocaml/
