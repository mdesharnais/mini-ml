# Mini ML

This is a compiler for a subset of ML developped as part of a *Praktikum* in
compiler construction at the LMU.

## Project goal

Goal: Compile the following OCaml-fragment to machine code using LLVM

    t ::=
        | i              (integer constant)
        | true
        | false
        | t op t         (op from =, <, +, -, *, /)
        | fun x -> t
        | t t
        | if t then t else t
        | let x = t in t
        | let rec f = t in t
        | print
        | (t)

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

## References

 - https://www.tcs.ifi.lmu.de/lehre/ws-2014-15/compilerbau/material/straightline.zip
 - https://www.tcs.ifi.lmu.de/lehre/ws-2014-15/compilerbau
 - http://caml.inria.fr/pub/docs/u3-ocaml/
