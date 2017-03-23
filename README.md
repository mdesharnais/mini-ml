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

## References

 - https://www.tcs.ifi.lmu.de/lehre/ws-2014-15/compilerbau/material/straightline.zip
 - https://www.tcs.ifi.lmu.de/lehre/ws-2014-15/compilerbau
 - http://caml.inria.fr/pub/docs/u3-ocaml/
