{-# LANGUAGE OverloadedLists #-}
import qualified Compiler
import qualified Data.Char
import qualified Expr
import qualified Data.Set as Set
import qualified Interpreter
import qualified Lexer
import qualified Parser
import qualified Type
import qualified TypeContext as TyCtxt
import qualified TypeInference as TyInferance

import Expr(Expr(..))
import Interpreter(Value(..))
import Test.HUnit
import Type
import TypeContext(Context)

litBool = [
    ("true", LitBool () True),
    ("false", LitBool () False)
  ]

litInt min max =
  let
    impl n xs =
      if n >= max then xs else impl (n + 1) ((show n, LitInt () n) : xs)
  in
    impl min []

variables = [
    ("a", Var () "a"),
    ("ab", Var () "ab"),
    ("ab1", Var () "ab1"),
    ("ab12", Var () "ab12"),
    ("ab121", Var () "ab121"),
    ("ab121b", Var () "ab121b"),
    ("ab121ba", Var () "ab121ba")
  ]

functions = [
    ("let min = fun x -> fun y -> if x < y then x else y in min 3 5",
      Let () ("min", ())
        (Abs () "x" (Abs () "y"
          (If () (OpLT () (Var () "x") (Var () "y"))
            (Var () "x")
            (Var () "y"))))
        (App () (App () (Var () "min") (LitInt () 3)) (LitInt () 5))),
    ("1 * 2 < 3 * 4",
      OpLT ()
        (OpMul () (LitInt () 1) (LitInt () 2))
        (OpMul () (LitInt () 3) (LitInt () 4)))
  ]

testCases =
  litBool ++
  litInt 0 101 ++
  variables ++
  functions

testEquivalences = [
    ("a * b * c", "(a * b) * c"),
    ("a + b * c", "a + (b * c)"),
    ("f x y z", "((f x) y) z"),
    ("f x + f y", "(f x) + (f y)"),
    ("a * b < c * d", "(a * b) < (c * d)"),
    ("extern f 5", "(extern f) 5"),
    ("let min = fun x -> fun y -> if x < y then x else y in min 2 3",
     "let min = (fun x -> (fun y -> (if (x < y) then x else y))) in ((min 2) 3)")
  ]

testInference :: [(Context, String, Expr TypeSchema Type)]
testInference =
  let int = LitInt TInt in
  let bool = LitBool TBool in [
    (TyCtxt.empty, "true", bool True),
    (TyCtxt.empty, "false", bool False),
    (TyCtxt.empty, "1", int 1),
    (TyCtxt.empty, "12", int 12),
    (TyCtxt.empty, "123", int 123),
    (TyCtxt.empty, "3 - 2", OpSub TInt (int 3) (int 2)),
    (TyCtxt.empty, "3 + 2", OpAdd TInt (int 3) (int 2)),
    (TyCtxt.empty, "3 * 2", OpMul TInt (int 3) (int 2)),
    (TyCtxt.empty, "3 / 2", OpDiv TInt (int 3) (int 2)),
    (TyCtxt.empty, "3 < 2", OpLT TBool (int 3) (int 2)),
    (TyCtxt.empty, "3 = 2", OpEQ TBool (int 3) (int 2)),

    (TyCtxt.empty, "if true then 0 else 1",
      If TInt (bool True) (int 0) (int 1)),

    (TyCtxt.empty, "extern f",
      ExternVar (TFun "x0" TInt TInt) "f"),

    (TyCtxt.empty, "fun x -> x",
      Abs (TFun "x1" (TVar "x0") (TVar "x0")) "x" (Var (TVar "x0") "x")),

    (TyCtxt.empty, "fun x -> fun y -> x",
      Abs (TFun "x3" (TVar "x0") (TFun "x2" (TVar "x1") (TVar "x0"))) "x"
        (Abs (TFun "x2" (TVar "x1") (TVar "x0")) "y"
          (Var (TVar "x0") "x"))),

    (TyCtxt.empty, "fun x -> fun y -> y",
      Abs (TFun "x3" (TVar "x0") (TFun "x2" (TVar "x1") (TVar "x1"))) "x"
        (Abs (TFun "x2" (TVar "x1") (TVar "x1")) "y"
          (Var (TVar "x1") "y"))),

    (TyCtxt.empty, "fun x -> true",
      Abs (TFun "x1" (TVar "x0") TBool) "x" (bool True)),
    (TyCtxt.empty, "let x = true in 3",
      Let TInt ("x", TSType TBool) (bool True) (int 3)),
    (TyCtxt.empty, "let min = fun x -> fun y -> if x < y then x else y in min 2 3",
      Let TInt ("min", (TSType (TFun "x3" TInt (TFun "x2" TInt TInt))))
        (Abs (TFun "x3" TInt (TFun "x2" TInt TInt)) "x"
          (Abs (TFun "x2" TInt TInt) "y"
            (If TInt (OpLT TBool (Var TInt "x") (Var TInt "y"))
              (Var TInt "x")
              (Var TInt "y"))))
        (App TInt
          (App (TFun "x2" TInt TInt)
            (Var (TFun "x3" TInt (TFun "x2" TInt TInt)) "min")
            (int 2))
          (int 3))),

    (TyCtxt.empty, "let rec f = fun x -> x in f 1",
      Let TInt ("f", TSForall "x0" (TSType (TFun "x2" (TVar "x0") (TVar "x0"))))
        (AbsRec (TFun "x2" (TVar "x0") (TVar "x0")) "f" "x" (Var (TVar "x0") "x"))
        (App TInt (Var (TFun "x2" TInt TInt) "f") (int 1))),

    (TyCtxt.empty, "let rec f = fun x -> fun y -> x in f 1 2",
      Let TInt ("f",TSForall "x3" (TSForall "x0"
        (TSType (TFun "x2" (TVar "x0") (TFun "x4" (TVar "x3") (TVar "x0"))))))
        (AbsRec (TFun "x2" (TVar "x0") (TFun "x4" (TVar "x3") (TVar "x0"))) "f" "x"
          (Abs (TFun "x4" (TVar "x3") (TVar "x0")) "y" (Var (TVar "x0") "x")))
        (App TInt
          (App (TFun "x4" TInt TInt)
            (Var (TFun "x2" TInt (TFun "x4" TInt TInt)) "f")
            (LitInt TInt 1))
        (LitInt TInt 2))),

    (TyCtxt.empty, "let rec sum = fun n -> if n = 0 then 0 else n + sum (n - 1) in sum 3",
      Let TInt ("sum", TSType (TFun "x2" TInt TInt))
        (AbsRec (TFun "x2" TInt TInt) "sum" "n"
          (If TInt (OpEQ TBool (Var TInt "n") (int 0))
            (int 0)
            (OpAdd TInt
              (Var TInt "n")
              (App TInt
                (Var (TFun "x2" TInt TInt) "sum")
                (OpSub TInt (Var TInt "n") (int 1))))))
        (App TInt (Var (TFun "x2" TInt TInt) "sum") (int 3))),

    (TyCtxt.empty, "let rec mult = fun x -> fun y -> if y < 1 then 0 else mult x (y - 1) in mult 3 5",
      Let TInt ("mult", TSType (TFun "" TInt (TFun "" TInt TInt)))
        (AbsRec (TFun "" TInt (TFun "" TInt TInt)) "mult" "x"
          (Abs (TFun "" TInt TInt) "y"
            (If TInt (OpLT TBool (Var TInt "y") (int 1))
              (int 0)
              (App TInt
                (App (TFun "" TInt TInt)
                  (Var (TFun "" TInt (TFun "" TInt TInt)) "mult")
                  (Var TInt "x"))
                (OpSub TInt (Var TInt "y") (int 1))))))
        (App TInt
          (App (TFun "" TInt TInt)
            (Var (TFun "" TInt (TFun "" TInt TInt)) "mult")
            (int 3))
          (int 5))),

    (TyCtxt.empty, "let f = fun x -> fun y -> if true then x else y in f 2 3",
      Let TInt ("f", TSForall "x0"
        (TSType (TFun "x3" (TVar "x0") (TFun "x2" (TVar "x0") (TVar "x0")))))
        (Abs (TFun "x3" (TVar "x0") (TFun "x2" (TVar "x0") (TVar "x0"))) "x"
          (Abs (TFun "x2" (TVar "x0") (TVar "x0")) "y"
            (If (TVar "x0") (bool True)
              (Var (TVar "x0") "x")
              (Var (TVar "x0") "y"))))
          (App TInt
            (App (TFun "x2" TInt TInt)
              (Var (TFun "x3" TInt (TFun "x2" TInt TInt)) "f")
              (int 2))
          (int 3))),
    (TyCtxt.empty, "let f = fun b -> fun x -> fun y -> if b then x else y in f true 2 3",
      Let TInt ("f", (TSForall "x1" (TSType
          (TFun "x5" TBool (TFun "x4" (TVar "x1") (TFun "x3" (TVar "x1") (TVar "x1")))))))
        (Abs (TFun "x5" TBool (TFun "x4" (TVar "x1") (TFun "x3" (TVar "x1") (TVar "x1")))) "b"
          (Abs (TFun "x4" (TVar "x1") (TFun "x3" (TVar "x1") (TVar "x1"))) "x"
            (Abs (TFun "x3" (TVar "x1") (TVar "x1")) "y"
              (If (TVar "x1") (Var TBool "b")
                (Var (TVar "x1") "x")
                (Var (TVar "x1") "y")))))
        (App TInt
          (App (TFun "x3" TInt TInt)
            (App (TFun "x4" TInt (TFun "x3" TInt TInt))
              (Var (TFun "x5" TBool (TFun "x4" TInt (TFun "x3" TInt TInt))) "f")
              (bool True))
            (int 2))
          (int 3))),
    (TyCtxt.empty, "let i = fun x -> x in if i true then i 1 else i 2",
      Let TInt ("i", TSForall "x0" (TSType (TFun "x1" (TVar "x0") (TVar "x0"))))
        (Abs (TFun "x1" (TVar "x0") (TVar "x0")) "x"
          (Var (TVar "x0") "x"))
        (If TInt (App TBool (Var (TFun "x1" TBool TBool) "i") (bool True))
          (App TInt (Var (TFun "x1" TInt TInt) "i") (int 1))
          (App TInt (Var (TFun "x1" TInt TInt) "i") (int 2)))),
    (TyCtxt.empty, "let foo = fun b -> if b then true else false in foo true",
      Let TBool ("foo", (TSType (TFun "x1" TBool TBool)))
        (Abs (TFun "x1" TBool TBool) "b"
          (If TBool (Var TBool "b")
            (bool True)
            (bool False)))
        (App TBool (Var (TFun "x1" TBool TBool) "foo") (bool True))),
    (TyCtxt.empty, "let rec f = fun x -> x in if f true then f 3 else f 4",
      (Let TInt ("f", TSForall "x0" (TSType (TFun "x2" (TVar "x0") (TVar "x0"))))
        (AbsRec(TFun "x2" (TVar "x0") (TVar "x0")) "f" "x" (Var (TVar "x0") "x"))
        (If TInt (App TBool (Var (TFun "x2" TBool TBool) "f") (bool True))
          (App TInt (Var (TFun "x2" TInt TInt) "f") (int 3))
          (App TInt (Var (TFun "x2" TInt TInt) "f") (int 4))))),
    (TyCtxt.empty,
      "let not = fun b -> if b then b else false in " ++
      "let rec foo = fun b -> fun x -> fun y -> " ++
        "if b then x else foo (not b) y x in " ++
      "foo false 1 1",
        Let TInt ("not", TSType (TFun "x1" TBool TBool))
          (Abs (TFun "x1" TBool TBool) "b"
            (If TBool (Var TBool "b")
              (Var TBool "b")
              (bool False)))
        (Let TInt ("foo", TSForall "x5" (TSType
          (TFun "x4" TBool
            (TFun "x16" (TVar "x5")
              (TFun "x15" (TVar "x5") (TVar "x5"))))))
          (AbsRec (TFun "x4" TBool
            (TFun "x16" (TVar "x5")
              (TFun "x15" (TVar "x5") (TVar "x5")))) "foo" "b"
            (Abs (TFun "x16" (TVar "x5") (TFun "x15" (TVar "x5") (TVar "x5"))) "x"
            (Abs (TFun "x15" (TVar "x5") (TVar "x5")) "y"
              (If (TVar "x5") (Var TBool "b")
                (Var (TVar "x5") "x")
                (App (TVar "x5")
                  (App (TFun "x14" (TVar "x5") (TVar "x5"))
                    (App (TFun "x12" (TVar "x5") (TFun "x14" (TVar "x5") (TVar "x5")))
                      (Var (TFun "x4" TBool (TFun "x12" (TVar "x5")
                        (TFun "x14" (TVar "x5") (TVar "x5")))) "foo")
                      (App TBool
                        (Var (TFun "x1" TBool TBool) "not")
                        (Var TBool "b")))
                    (Var (TVar "x5") "y"))
                  (Var (TVar "x5") "x"))))))
          (App TInt
            (App (TFun "x15" TInt TInt)
              (App (TFun "x16" TInt (TFun "x15" TInt TInt))
                (Var (TFun "x4" TBool (TFun "x16" TInt (TFun "x15" TInt TInt))) "foo")
                (bool False))
              (int 1))
            (int 1)))),
    (TyCtxt.empty, "fun fix -> fun f -> f (fun y -> fix f y)",
      Abs
        (TFun "x11"
          (TFun "x4"
            (TFun "x9" (TFun "x7" (TVar "x2") (TVar "x5")) (TVar "x8"))
            (TFun "x6" (TVar "x2") (TVar "x5")))
          (TFun "x10"
            (TFun "x9" (TFun "x7" (TVar "x2") (TVar "x5")) (TVar "x8"))
            (TVar "x8")))
        "fix"
        (Abs
          (TFun "x10"
            (TFun "x9" (TFun "x7" (TVar "x2") (TVar "x5")) (TVar "x8"))
            (TVar "x8"))
          "f"
          (App (TVar "x8")
            (Var (TFun "x9" (TFun "x7" (TVar "x2") (TVar "x5")) (TVar "x8")) "f")
            (Abs (TFun "x7" (TVar "x2") (TVar "x5")) "y"
              (App (TVar "x5")
                (App (TFun "x6" (TVar "x2") (TVar "x5"))
                  (Var
                    (TFun "x4"
                      (TFun "x9" (TFun "x7" (TVar "x2") (TVar "x5")) (TVar "x8"))
                      (TFun "x6" (TVar "x2") (TVar "x5"))) "fix")
                  (Var (TFun "x9" (TFun "x7" (TVar "x2") (TVar "x5")) (TVar "x8")) "f"))
                (Var (TVar "x2") "y")))))
      ),
    (TyCtxt.empty, "let rec fix = fun f -> f (fun y -> fix f y) in fix",
    Let
      (TFun "x2"
        (TFun "x10"
          (TFun "x8" (TVar "x12") (TVar "x11"))
          (TFun "x7" (TVar "x12") (TVar "x11")))
        (TFun "x7" (TVar "x12") (TVar "x11")))
      ("fix",
        TSForall "x6" (TSForall "x3" (TSType (TFun "x2"
          (TFun "x10"
            (TFun "x8" (TVar "x3") (TVar "x6"))
            (TFun "x7" (TVar "x3") (TVar "x6")))
          (TFun "x7" (TVar "x3") (TVar "x6"))))))
      (AbsRec
        (TFun "x2"
          (TFun "x10"
            (TFun "x8" (TVar "x3") (TVar "x6"))
            (TFun "x7" (TVar "x3") (TVar "x6")))
          (TFun "x7" (TVar "x3") (TVar "x6"))) "fix" "f"
        (App (TFun "x7" (TVar "x3") (TVar "x6"))
          (Var
            (TFun "x10"
              (TFun "x8" (TVar "x3") (TVar "x6"))
              (TFun "x7" (TVar "x3") (TVar "x6"))) "f")
          (Abs (TFun "x8" (TVar "x3") (TVar "x6")) "y"
            (App (TVar "x6")
              (App (TFun "x7" (TVar "x3") (TVar "x6"))
                (Var
                  (TFun "x2"
                    (TFun "x10"
                      (TFun "x8" (TVar "x3") (TVar "x6"))
                      (TFun "x7" (TVar "x3") (TVar "x6")))
                    (TFun "x7" (TVar "x3") (TVar "x6")))
                  "fix")
                (Var
                  (TFun "x10"
                    (TFun "x8" (TVar "x3") (TVar "x6"))
                    (TFun "x7" (TVar "x3") (TVar "x6")))
                  "f"))
              (Var (TVar "x3") "y")))))
        (Var
          (TFun "x2"
            (TFun "x10"
              (TFun "x8" (TVar "x12") (TVar "x11"))
              (TFun "x7" (TVar "x12") (TVar "x11")))
            (TFun "x7" (TVar "x12") (TVar "x11")))
          "fix")),
    (TyCtxt.empty,
      "fun f -> f (fun x -> f (fun y -> y))",
      Abs (TFun "x9" (TFun "x5" (TFun "x3" (TVar "x2") (TVar "x2")) (TVar "x2")) (TVar "x2")) "f"
        (App (TVar "x2")
          (Var (TFun "x5" (TFun "x3" (TVar "x2") (TVar "x2")) (TVar "x2")) "f")
          (Abs (TFun "x3" (TVar "x2") (TVar "x2")) "x"
            (App (TVar "x2")
              (Var (TFun "x5" (TFun "x3" (TVar "x2") (TVar "x2")) (TVar "x2")) "f")
              (Abs (TFun "x3" (TVar "x2") (TVar "x2")) "y"
                (Var (TVar "x2") "y")))))),
    (TyCtxt.empty,
      "fun f -> f (fun x -> f (fun y -> x))",
      Abs (TFun "x9" (TFun "x5" (TFun "x3" (TVar "x2") (TVar "x2")) (TVar "x2")) (TVar "x2")) "f"
        (App (TVar "x2")
          (Var (TFun "x5" (TFun "x3" (TVar "x2") (TVar "x2")) (TVar "x2")) "f")
          (Abs (TFun "x3" (TVar "x2") (TVar "x2")) "x"
            (App (TVar "x2")
              (Var (TFun "x5" (TFun "x3" (TVar "x2") (TVar "x2")) (TVar "x2")) "f")
              (Abs (TFun "x3" (TVar "x2") (TVar "x2")) "y"
                (Var (TVar "x2") "x")))))),
    (TyCtxt.singleton ("x", TInt), "x",
      Var TInt "x"),

    (TyCtxt.singleton ("f", TFun "" TInt TInt), "f",
      Var (TFun "" TInt TInt) "f"),

    (TyCtxt.singleton ("f", TFun "" TInt TInt), "f 3",
      App TInt (Var (TFun "" TInt TInt) "f") (int 3)),

    (TyCtxt.singleton ("x", TVar "x0"), "x - 1",
      OpSub TInt (Var TInt "x") (int 1)),

    (TyCtxt.fromListTy [("x", TVar "x0"), ("y", TVar "x1")], "x y",
      App (TVar "x2")
        (Var (TFun "x3" (TVar "x1") (TVar "x2")) "x")
        (Var (TVar "x1") "y")),

    (TyCtxt.empty,
      "let n = 10 in " ++
      "let foo = fun g -> g 10 in " ++
      "foo (fun x -> x + n) + foo (fun x -> x)",
      Let TInt ("n",TSType TInt) (int 10)
      (Let TInt ("foo",TSForall "x1"
        (TSType (TFun "x3" (TFun "x2" TInt (TVar "x1")) (TVar "x1"))))
        (Abs (TFun "x3" (TFun "x2" TInt (TVar "x1")) (TVar "x1")) "g"
          (App (TVar "x1")
            (Var (TFun "x2" TInt (TVar "x1")) "g") (int 10)))
        (OpAdd TInt
          (App TInt (Var (TFun "x3" (TFun "x2" TInt TInt) TInt) "foo")
            (Abs (TFun "x2" TInt TInt) "x"
              (OpAdd TInt (Var TInt "x") (Var TInt "n"))))
          (App TInt
            (Var (TFun "x3" (TFun "x2" TInt TInt) TInt) "foo")
            (Abs (TFun "x2" TInt TInt) "x" (Var TInt "x"))))))
  ]

testInference2 :: [(String, TyExpr2)]
testInference2 =
  let int = LitInt TInt in
  let bool = LitBool TBool in [
    ("fun x -> x",
      Abs (TFun [AFun] (TVar "x0") (TVar "x0")) "x"
        (Var (TVar "x0") "x")),

    ("fun x -> fun y -> y",
      Abs (TFun [AFun] (TVar "x0") (TFun [AFun] (TVar "x1") (TVar "x1"))) "x"
        (Abs (TFun [AFun] (TVar "x1") (TVar "x1")) "y"
          (Var (TVar "x1") "y"))),

    ("fun x -> fun y -> x",
      Abs (TFun [AFun] (TVar "x0") (TFun [AClo] (TVar "x1") (TVar "x0"))) "x"
        (Abs (TFun [AClo] (TVar "x1") (TVar "x0")) "y"
          (Var (TVar "x0") "x"))),

    ("let f = fun x -> x + 10 in f 10 ",
      Let TInt ("f",TSType (TFun [AFun] TInt TInt))
        (Abs (TFun [AFun] TInt TInt) "x"
          (OpAdd TInt (Var TInt "x") (LitInt TInt 10)))
        (App TInt
          (Var (TFun [AFun] TInt TInt) "f")
          (LitInt TInt 10))),

    ("let n = 10 in fun x -> x + n",
      Let (TFun [AClo] TInt TInt) ("n",TSType TInt)
        (LitInt TInt 10)
        (Abs (TFun [AClo] TInt TInt) "x"
          (OpAdd TInt (Var TInt "x") (Var TInt "n")))),

    ("let n = 10 in let f = fun x -> x + n in f 10 ",
      Let TInt ("n",TSType TInt) (LitInt TInt 10)
      (Let TInt ("f",TSType (TFun [AClo] TInt TInt))
        (Abs (TFun [AClo] TInt TInt) "x"
          (OpAdd TInt (Var TInt "x") (Var TInt "n")))
        (App TInt (Var (TFun [AClo] TInt TInt) "f") (LitInt TInt 10)))),

    ("fun g -> g 10",
      Abs (TFun [AFun] (TFun [] TInt (TVar "x1")) (TVar "x1")) "g"
        (App (TVar "x1") (Var (TFun [] TInt (TVar "x1")) "g") (LitInt TInt 10))),

    ("let n = 10 in " ++
     "let f = fun x -> x + 10 in " ++
     "let c = fun x -> x + n in " ++
     "let foo = fun g -> g 10 in " ++
     "foo f",
      Let TInt ("n",TSType TInt) (LitInt TInt 10)
      (Let TInt ("f",TSType (TFun [AFun] TInt TInt))
        (Abs (TFun [AFun] TInt TInt) "x"
          (OpAdd TInt (Var TInt "x") (LitInt TInt 10)))
      (Let TInt ("c",TSType (TFun [AClo] TInt TInt))
        (Abs (TFun [AClo] TInt TInt) "x"
          (OpAdd TInt (Var TInt "x") (Var TInt "n")))
      (Let TInt ("foo",TSForall "x5" (TSType
        (TFun [AFun] (TFun [AFun] TInt (TVar "x5")) (TVar "x5"))))
        (Abs (TFun [AFun] (TFun [AFun] TInt (TVar "x5")) (TVar "x5")) "g"
          (App (TVar "x5")
            (Var (TFun [AFun] TInt (TVar "x5")) "g")
            (LitInt TInt 10)))
        (App TInt
          (Var (TFun [AFun] (TFun [AFun] TInt TInt) TInt) "foo")
          (Var (TFun [AFun] TInt TInt) "f")))))),

    ("let n = 10 in " ++
     "let f = fun x -> x + 10 in " ++
     "let c = fun x -> x + n in " ++
     "let foo = fun g -> g 10 in " ++
     "foo c",
      Let TInt ("n",TSType TInt) (LitInt TInt 10)
      (Let TInt ("f",TSType (TFun [AFun] TInt TInt))
        (Abs (TFun [AFun] TInt TInt) "x"
          (OpAdd TInt (Var TInt "x") (LitInt TInt 10)))
      (Let TInt ("c",TSType (TFun [AClo] TInt TInt))
        (Abs (TFun [AClo] TInt TInt) "x"
          (OpAdd TInt (Var TInt "x") (Var TInt "n")))
      (Let TInt ("foo",TSForall "x5" (TSType
        (TFun [AFun] (TFun [AClo] TInt (TVar "x5")) (TVar "x5"))))
        (Abs (TFun [AFun] (TFun [AClo] TInt (TVar "x5")) (TVar "x5")) "g"
          (App (TVar "x5")
            (Var (TFun [AClo] TInt (TVar "x5")) "g")
            (LitInt TInt 10)))
        (App TInt
          (Var (TFun [AFun] (TFun [AClo] TInt TInt) TInt) "foo")
          (Var (TFun [AClo] TInt TInt) "c")))))),

    ("let n = 10 in " ++
     "let foo = fun g -> g 10 in " ++
     "foo (fun x -> x + n) + foo (fun x -> x)",
      Let TInt ("n",TSType TInt) (int 10)
      (Let TInt ("foo",TSForall "x1"
        (TSType (TFun [AFun] (TFun [AFun,AClo] TInt (TVar "x1")) (TVar "x1"))))
        (Abs (TFun [AFun] (TFun [AFun,AClo] TInt (TVar "x1")) (TVar "x1")) "g"
          (App (TVar "x1")
            (Var (TFun [AFun,AClo] TInt (TVar "x1")) "g") (int 10)))
        (OpAdd TInt
          (App TInt
            (Var (TFun [AFun] (TFun [AFun,AClo] TInt TInt) TInt) "foo")
            (Abs (TFun [AFun,AClo] TInt TInt) "x"
              (OpAdd TInt (Var TInt "x") (Var TInt "n"))))
          (App TInt
            (Var (TFun [AFun] (TFun [AFun,AClo] TInt TInt) TInt) "foo")
            (Abs (TFun [AFun,AClo] TInt TInt) "x" (Var TInt "x")))))),

    ("let n = 10 in " ++
     "let foo = fun g -> g 10 in " ++
     "foo (fun x -> x) + foo (fun x -> x + n)",
      Let TInt ("n",TSType TInt) (int 10)
      (Let TInt ("foo",TSForall "x1"
        (TSType (TFun [AFun] (TFun [AFun,AClo] TInt (TVar "x1")) (TVar "x1"))))
        (Abs (TFun [AFun] (TFun [AFun,AClo] TInt (TVar "x1")) (TVar "x1")) "g"
          (App (TVar "x1")
            (Var (TFun [AFun,AClo] TInt (TVar "x1")) "g") (int 10)))
        (OpAdd TInt
          (App TInt
            (Var (TFun [AFun] (TFun [AFun,AClo] TInt TInt) TInt) "foo")
            (Abs (TFun [AFun,AClo] TInt TInt) "x" (Var TInt "x")))
          (App TInt
            (Var (TFun [AFun] (TFun [AFun,AClo] TInt TInt) TInt) "foo")
            (Abs (TFun [AFun,AClo] TInt TInt) "x"
              (OpAdd TInt (Var TInt "x") (Var TInt "n"))))))),

    ("let n = 10 in " ++
     "let f = fun x -> x + 10 in " ++
     "let g = fun x -> x + n in " ++
     "let foo = fun g -> g 10 in " ++
     "(foo f) + (foo g)",
      Let TInt ("n",TSType TInt) (int 10)
      (Let TInt ("f",TSType (TFun [AFun,AClo] TInt TInt))
        (Abs (TFun [AFun,AClo] TInt TInt) "x"
          (OpAdd TInt (Var TInt "x") (int 10)))
      (Let TInt ("g",TSType (TFun [AFun,AClo] TInt TInt))
        (Abs (TFun [AFun, AClo] TInt TInt) "x"
          (OpAdd TInt (Var TInt "x") (Var TInt "n")))
      (Let TInt ("foo",TSForall "x5" (TSType
        (TFun [AFun] (TFun [AFun,AClo] TInt (TVar "x5")) (TVar "x5"))))
        (Abs (TFun [AFun] (TFun [AFun,AClo] TInt (TVar "x5")) (TVar "x5")) "g"
          (App (TVar "x5")
            (Var (TFun [AFun,AClo] TInt (TVar "x5")) "g")
            (LitInt TInt 10)))
      (OpAdd TInt
        (App TInt
          (Var (TFun [AFun] (TFun [AFun,AClo] TInt TInt) TInt) "foo")
          (Var (TFun [AFun,AClo] TInt TInt) "f"))
        (App TInt
          (Var (TFun [AFun] (TFun [AFun,AClo] TInt TInt) TInt) "foo")
          (Var (TFun [AFun,AClo] TInt TInt) "g")))))))
  ]

interpretationTests = [
    ("4 + 2", ConstInt 6),
    ("4 - 2", ConstInt 2),
    ("4 * 2", ConstInt 8),
    ("4 / 2", ConstInt 2),
    ("6 + 4 / 2", ConstInt 8),
    ("2 * 3 + 4 / 2", ConstInt 8),
    ("2 < 4", ConstBool True),
    ("4 < 2", ConstBool False),
    ("let i = fun x -> x in i 0", ConstInt 0),
    ("let i = fun x -> x in if i true then i 1 else i 2", ConstInt 1),
    ("let rec sum = fun n -> if n = 0 then 0 else n + sum (n - 1) in sum 3", ConstInt 6)
  ]

normalFormTests = [
    ("1", "1"),

    ("fun x -> x",
     "let x0 = (fun x -> x) in\n" ++
     "x0"),

    ("1 + 2",
     "let x0 = 1 + 2 in\nx0"),

    ("1 + 2 + 3",
     "let x0 = 1 + 2 in\nlet x1 = x0 + 3 in\nx1"),

    ("1 + 2 + 3 + 4",
     "let x0 = 1 + 2 in\nlet x1 = x0 + 3 in\nlet x2 = x1 + 4 in\nx2"),

    ("(fun x -> x) true",
     "let x0 = (fun x -> x) in\n" ++
     "let x1 = x0 true in\n" ++
     "x1"),

    ("let f = fun x -> fun y -> fun z -> x in f 1 2 3",
     "let x0 = (fun x -> " ++
       "let x1 = (fun y -> " ++
         "let x2 = (fun z -> x) in\nx2) in\nx1) in\n" ++
     "let x3 = x0 1 in\n" ++
     "let x4 = x3 2 in\n" ++
     "let x5 = x4 3 in\n" ++
     "x5"),

    ("(fun x -> x) (fun x -> x) true",
     "let x0 = (fun x -> x) in\n" ++
     "let x1 = (fun x -> x) in\n" ++
     "let x2 = x0 x1 in\n" ++
     "let x3 = x2 true in\n" ++
     "x3"),

    ("let a = 1 in let b = 2 in a * b",
     "let x0 = 1 * 2 in\nx0"),

    ("let f = fun x -> x in f 1",
     "let x0 = (fun x -> x) in\n" ++
     "let x1 = x0 1 in\n" ++
     "x1"),

    ("let f = fun x -> x in f 1 + f 2",
     "let x0 = (fun x -> x) in\n" ++
     "let x1 = x0 1 in\n" ++
     "let x2 = x0 2 in\n" ++
     "let x3 = x1 + x2 in\n" ++
     "x3"),

    ("let a = 1 in let b = 2 in 3 + a * b",
     "let x0 = 1 * 2 in\nlet x1 = 3 + x0 in\nx1"),

    ("if true then 1 else 2",
     "let x0 = if true then 1 else 2 in\nx0"),

    ("let f = fun x -> x in if true then f 1 else f 2",
     "let x0 = (fun x -> x) in\n" ++
     "let x1 = " ++
      "if true then " ++
        "let x2 = x0 1 in\nx2 " ++
      "else " ++
        "let x3 = x0 2 in\nx3 in\n" ++
     "x1"),

    ("let f = fun x -> if x then 1 else 2 in f true",
     "let x0 = (fun x -> " ++
        "let x1 = if x then 1 else 2 in\n" ++
        "x1) in\n" ++
     "let x2 = x0 true in\n" ++
     "x2"),

    ("let rec f = fun x -> fun y -> f y x in f 1 2",
     "let rec x0 = (fun x -> " ++
       "let x1 = (fun y -> " ++
         "let x2 = x0 y in\n" ++
         "let x3 = x2 x in\n" ++
         "x3) in\n" ++
       "x1) in\n" ++
     "let x4 = x0 1 in\n" ++
     "let x5 = x4 2 in\n" ++
     "x5"),

    ("let rec sum = fun n -> if n = 0 then 0 else n + sum (n - 1) in sum 3",
     "let rec x0 = (fun n -> " ++
       "let x1 = n = 0 in\n" ++
       "let x2 = if x1 then 0 else " ++
         "let x3 = n - 1 in\n" ++
         "let x4 = x0 x3 in\n" ++
         "let x5 = n + x4 in\n" ++
         "x5 in\n" ++
       "x2) in\n" ++
     "let x6 = x0 3 in\n" ++
     "x6"),

    ("let x = 5 in let f = fun y -> x + y in f 3",
     "let x0 = (fun y -> " ++
        "let x1 = 5 + y in\n" ++
        "x1) in\n" ++
     "let x2 = x0 3 in\n" ++
     "x2")
  ]

fvTests = [
    (TyCtxt.empty, "fun x -> x", []),
    (TyCtxt.singleton ("y", TInt), "fun x -> y", ["y"]),
    (TyCtxt.singleton ("y", TInt), "fun x -> x + y", ["y"]),
    (TyCtxt.empty, "let x = 2 + 3 in x", []),
    (TyCtxt.empty, "let x = 5 in let f = fun y -> x + y in f 3", []),
    (TyCtxt.singleton ("sum", TFun "" TInt TInt), "fun n -> if n = 0 then 0 else n + sum (n - 1)", ["sum"])
  ]

closureTests = [
    ("let n = 1 * 5 in " ++
     "let f = fun x -> fun y -> x + y + n in " ++
     "f 1 2",

     "let x0 = 1 * 5 in\n" ++
     "let x1 = Closure (fun env -> fun x -> " ++
       "let x2 = Closure (fun env -> fun y -> " ++
         "let x3 = env.0 + y in\n" ++
         "let x4 = x3 + env.1 in\n" ++
         "x4, [x,env.0]) in\n" ++
       "x2, [x0]) in\n" ++
     "let x5 = x1 1 in\n" ++
     "let x6 = x5 2 in\n" ++
     "x6"),

    ("let x = 5 in let f = fun y -> x + y in f 3",
     "let x0 = Closure (fun env -> fun y -> " ++
        "let x1 = 5 + y in\n" ++
        "x1, []) in\n" ++
     "let x2 = x0 3 in\n" ++
     "x2"),

    ("let rec f = fun x -> fun y -> f y x in f 1 2",
     "let x0 = Closure (fun env -> fun x -> " ++
       "let x1 = Closure (fun env -> fun y -> " ++
         "let x2 = env.0 y in\n" ++
         "let x3 = x2 env.1 in\n" ++
         "x3, [env.self,x]) in\n" ++
       "x1, []) in\n" ++
     "let x4 = x0 1 in\n" ++
     "let x5 = x4 2 in\n" ++
     "x5"),

    ("let x = 5 + 3 in let f = fun y -> x + y in f 3",
     "let x0 = 5 + 3 in\n" ++
     "let x1 = Closure (fun env -> fun y -> " ++
        "let x2 = env.0 + y in\n" ++
        "x2, [x0]) in\n" ++
     "let x3 = x1 3 in\n" ++
     "x3"),

    ("let rec sum = fun n -> if n = 0 then 0 else n + sum (n - 1) in sum 3",
     "let x0 = Closure (fun env -> fun n -> " ++
        "let x1 = n = 0 in\n" ++
        "let x2 = if x1 then 0 else " ++
          "let x3 = n - 1 in\n" ++
          "let x4 = env.self x3 in\n" ++
          "let x5 = n + x4 in\n" ++
          "x5 in\n" ++
        "x2, []) in\n" ++
      "let x6 = x0 3 in\n" ++
      "x6")

  ]

testCompilation :: (String, Expr () ()) -> Test
testCompilation (prog, expected) =
  TestLabel ("program is '" ++ prog ++ "'") $
    TestCase $
      assertEqual prog expected (Parser.parse (Lexer.alexScanTokens prog))

testComparaison :: (String, String) -> Test
testComparaison (prog1, prog2) =
  TestLabel ("program are '" ++ prog1 ++ "' and '" ++ prog2 ++ "'") $
    TestCase $
      assertEqual prog1
        (Parser.parse (Lexer.alexScanTokens prog1))
        (Parser.parse (Lexer.alexScanTokens prog2))

testTypeInference :: (Context, String, Expr TypeSchema Type) -> Test
testTypeInference (ctxt, prog, expr) =
  let term = Parser.parse (Lexer.alexScanTokens prog)
   in TestLabel ("program '" ++ prog ++ "' has type '" ++
        show (Expr.getType expr) ++ "'") $
        TestCase $
          case TyInferance.infer ctxt term of
            Right (subst, cs, expr') ->
              assertEqual (show subst) expr expr'
            Left msg -> assertFailure msg

testTypeInference2 :: (String, TyExpr2) -> Test
testTypeInference2 (prog, expr) =
  let term = Parser.parse (Lexer.alexScanTokens prog)
   in TestLabel ("program '" ++ prog ++ "' has type '" ++
        show (Expr.getType expr) ++ "'") $
        TestCase $
          case TyInferance.infer2 TyCtxt.empty term of
            Right expr' -> assertEqual "" expr expr'
            Left msg -> assertFailure msg

testInterpreter :: (String, Value () ()) -> Test
testInterpreter (prog, val) =
  let term = Parser.parse (Lexer.alexScanTokens prog)
   in TestLabel ("program '" ++ prog ++ "' evaluate to '" ++ show val ++ "'") $
        TestCase $
          case Interpreter.eval [] term of
            Just v -> assertEqual "" val v
            Nothing -> assertFailure "evaluation went wrong"

testNormalForm :: (String, String) -> Test
testNormalForm (prog, nf) =
  let term = Parser.parse (Lexer.alexScanTokens prog) in
  TestLabel prog $ TestCase $
    case TyInferance.infer2 TyCtxt.empty term of
      Left msg -> assertFailure msg
      Right expr -> assertEqual "" nf (show (Compiler.toNormalForm expr))

testFreeVariables :: (Context, String, [String]) -> Test
testFreeVariables (ctxt, prog, fvs) =
  let term = Parser.parse (Lexer.alexScanTokens prog) in
  TestLabel prog $ TestCase $
    case TyInferance.infer2 ctxt term of
      Left msg -> assertFailure msg
      Right expr ->
        assertEqual "" fvs (map fst (Compiler.fv (Compiler.toNormalForm expr)))

testClosure :: (String, String) -> Test
testClosure (prog, nfc) =
  let term = Parser.parse (Lexer.alexScanTokens prog) in
  TestLabel prog $ TestCase $
    case TyInferance.infer2 TyCtxt.empty term of
      Left msg -> assertFailure msg
      Right expr ->
        let normForm = Compiler.toNormalForm expr in
        let normFormClosure = Compiler.toClosure normForm in
        assertEqual "" nfc (show normFormClosure)

tests =
  TestList $ [
    TestLabel "testing (Parser.parse . Lexer.alexScanTokens)" $
      TestList (map testCompilation testCases),
    TestLabel "testing (parse prog1 == parse prog2)" $
      TestList (map testComparaison testEquivalences),
    TestLabel "testing (infer (parse prog))" $
      TestList (map testTypeInference testInference),
    TestLabel "testing (infer2 (parse prog))" $
      TestList (map testTypeInference2 testInference2),
    TestLabel "testing (eval [] (parse prog))" $
      TestList (map testInterpreter interpretationTests),
    TestLabel "testing (toNormalForm (parse prog))" $
      TestList (map testNormalForm normalFormTests),
    TestLabel "Compiler.fv" $
      TestList (map testFreeVariables fvTests),
    TestLabel "Compiler.toClosure" $
      TestList (map testClosure closureTests)
  ]

main :: IO ()
main = fmap (const ()) (runTestTT tests)
