import qualified Compiler
import qualified Data.Char
import qualified Expr
import qualified Interpreter
import qualified Lexer
import qualified Parser
--import qualified Type
--import qualified TypeContext as TyContext
import qualified TypeInference2 as TyInferance

import Expr(Expr(..))
import Interpreter(Value(..))
import Test.HUnit
import TypeInference2(TVar(..), AVar(..), SType(..), Context)
--import Type(Type(..), TypeSchema(..))
--import TypeContext(Context)

type Type = SType
var = STVar . TVar
tsType = id
tsForall _ = id

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

testInference :: [(Context, String, Expr Type Type)]
testInference =
  let int = LitInt STInt in
  let bool = LitBool STBool in [
    ([], "true", bool True),
    ([], "false", bool False),
    ([], "1", int 1),
    ([], "12", int 12),
    ([], "123", int 123),
    ([], "3 - 2", OpSub STInt (int 3) (int 2)),
    ([], "3 + 2", OpAdd STInt (int 3) (int 2)),
    ([], "3 * 2", OpMul STInt (int 3) (int 2)),
    ([], "3 / 2", OpDiv STInt (int 3) (int 2)),
    ([], "3 < 2", OpLT STBool (int 3) (int 2)),
    ([], "3 = 2", OpEQ STBool (int 3) (int 2)),
    ([], "if true then 0 else 1",
      If STInt (bool True) (int 0) (int 1)),
    ([], "extern f",
      ExternVar (STFun (AVar "x0") STInt STInt) "f"),
    ([], "fun x -> x",
      Abs (STFun (AVar "x1") (var "x0") (var "x0")) "x" (Var (var "x0") "x")),
    ([], "fun x -> true",
      Abs (STFun (AVar "x1") (var "x0") STBool) "x" (bool True)),
    ([], "let f = fun x -> true in 3",
      Let STInt
        ("f", (STFun (AVar "x1") (var "x0") STBool))
        (Abs (STFun (AVar "x1") (var "x0") STBool) "x" (bool True))
        (int 3)),
    ([], "fun x -> fun y -> true",
      Abs
        (STFun (AVar "x3")
          (STVar (TVar "x0"))
          (STFun (AVar "x2") (STVar (TVar "x1")) STBool)) "x"
        (Abs
          (STFun (AVar "x2") (STVar (TVar "x1")) STBool) "y"
          (bool True))),
    ([], "fun x -> fun y -> if true then x else y",
      Abs
        (STFun (AVar "x3")
          (STVar (TVar "x0"))
          (STFun (AVar "x2") (STVar (TVar "x1")) STBool)) "x"
        (Abs
          (STFun (AVar "x2") (STVar (TVar "x1")) STBool) "y"
          (bool True))),
    ([], "let x = true in 3",
      Let STInt ("x",  STBool) (bool True) (int 3)),
    ([], "let min = fun x -> fun y -> if x < y then x else y in min 2 3",
      Let STInt ("min", (tsType (STFun (AVar "") STInt (STFun (AVar "") STInt STInt))))
        (Abs (STFun (AVar "") STInt (STFun (AVar "") STInt STInt)) "x"
          (Abs (STFun (AVar "") STInt STInt) "y"
            (If STInt (OpLT STBool (Var STInt "x") (Var STInt "y"))
              (Var STInt "x")
              (Var STInt "y"))))
        (App STInt
          (App (STFun (AVar "") STInt STInt)
            (Var (STFun (AVar "") STInt (STFun (AVar "") STInt STInt)) "min")
            (int 2))
          (int 3))),
    ([], "let rec sum = fun n -> if n = 0 then 0 else n + sum (n - 1) in sum 3",
      LetRec STInt ("sum", tsType (STFun (AVar "") STInt STInt))
        ("n",
          (If STInt (OpEQ STBool (Var STInt "n") (int 0))
            (int 0)
            (OpAdd STInt
              (Var STInt "n")
              (App STInt
                (Var (STFun (AVar "") STInt STInt) "sum")
                (OpSub STInt (Var STInt "n") (int 1))))))
        (App STInt (Var (STFun (AVar "") STInt STInt) "sum") (int 3))),
    ([], "let f = fun x -> fun y -> if true then x else y in f 2 3",
      Let STInt ("f", tsForall "x1" (tsType (STFun (AVar "") (var "x1") (STFun (AVar "") (var "x1") (var "x1")))))
        (Abs (STFun (AVar "") (var "x1") (STFun (AVar "") (var "x1") (var "x1"))) "x"
          (Abs (STFun (AVar "") (var "x1") (var "x1")) "y"
            (If (var "x1") (bool True)
              (Var (var "x1") "x")
              (Var (var "x1") "y"))))
          (App STInt
            (App (STFun (AVar "") STInt STInt)
              (Var (STFun (AVar "") STInt (STFun (AVar "") STInt STInt)) "f")
              (int 2))
          (int 3))),
    ([], "let f = fun b -> fun x -> fun y -> if b then x else y in f true 2 3",
      Let STInt ("f", (tsForall "x2" (tsType
          (STFun (AVar "") STBool (STFun (AVar "") (var "x2") (STFun (AVar "") (var "x2") (var "x2")))))))
        (Abs (STFun (AVar "") STBool (STFun (AVar "") (var "x2") (STFun (AVar "") (var "x2") (var "x2")))) "b"
          (Abs (STFun (AVar "") (var "x2") (STFun (AVar "") (var "x2") (var "x2"))) "x"
            (Abs (STFun (AVar "") (var "x2") (var "x2")) "y"
              (If (var "x2") (Var STBool "b")
                (Var (var "x2") "x")
                (Var (var "x2") "y")))))
        (App STInt
          (App (STFun (AVar "") STInt STInt)
            (App (STFun (AVar "") STInt (STFun (AVar "") STInt STInt))
              (Var (STFun (AVar "") STBool (STFun (AVar "") STInt (STFun (AVar "") STInt STInt))) "f")
              (bool True))
            (int 2))
          (int 3))),
    ([], "let i = fun x -> x in if i true then i 1 else i 2",
      Let STInt ("i", tsForall "x0" (tsType (STFun (AVar "") (var "x0") (var "x0"))))
        (Abs (STFun (AVar "") (var "x0") (var "x0")) "x"
          (Var (var "x0") "x"))
        (If STInt (App STBool (Var (STFun (AVar "") STBool STBool) "i") (bool True))
          (App STInt (Var (STFun (AVar "") STInt STInt) "i") (int 1))
          (App STInt (Var (STFun (AVar "") STInt STInt) "i") (int 2)))),
    ([], "let foo = fun b -> if b then true else false in foo true",
      Let STBool ("foo", (tsType (STFun (AVar "") STBool STBool)))
        (Abs (STFun (AVar "") STBool STBool) "b"
          (If STBool (Var STBool "b")
            (bool True)
            (bool False)))
        (App STBool (Var (STFun (AVar "") STBool STBool) "foo") (bool True))),
    ([], "let rec f = fun x -> x in if f true then f 3 else f 4",
      (LetRec STInt ("f", tsForall "x1" (tsType (STFun (AVar "") (var "x1") (var "x1"))))
        ("x", (Var (var "x1")) "x")
        (If STInt (App STBool (Var (STFun (AVar "") STBool STBool) "f") (bool True))
          (App STInt (Var (STFun (AVar "") STInt STInt) "f") (int 3))
          (App STInt (Var (STFun (AVar "") STInt STInt) "f") (int 4))))),
    ([],
      "let not = fun b -> if b then b else false in " ++
      "let rec foo = fun b -> fun x -> fun y -> " ++
        "if b then x else foo (not b) y x in " ++
      "foo false 1 1",
        Let STInt ("not", tsType (STFun (AVar "") STBool STBool))
          (Abs (STFun (AVar "") STBool STBool) "b"
            (If STBool (Var STBool "b")
              (Var STBool "b")
              (bool False)))
        (LetRec STInt ("foo", tsForall "x8" (tsType
          (STFun (AVar "") STBool (STFun (AVar "") (var "x8") (STFun (AVar "") (var "x8") (var "x8"))))))
          ("b", Abs (STFun (AVar "") (var "x8") (STFun (AVar "") (var "x8") (var "x8"))) "x"
            (Abs (STFun (AVar "") (var "x8") (var "x8")) "y"
              (If (var "x8") (Var STBool "b")
                (Var (var "x8") "x")
                (App (var "x8")
                  (App (STFun (AVar "") (var "x8") (var "x8"))
                    (App (STFun (AVar "") (var "x8") (STFun (AVar "") (var "x8") (var "x8")))
                      (Var (STFun (AVar "") STBool (STFun (AVar "") (var "x8")
                        (STFun (AVar "") (var "x8") (var "x8")))) "foo")
                      (App STBool
                        (Var (STFun (AVar "") STBool STBool) "not")
                        (Var STBool "b")))
                    (Var (var "x8") "y"))
                  (Var (var "x8") "x")))))
          (App STInt
            (App (STFun (AVar "") STInt STInt)
              (App (STFun (AVar "") STInt (STFun (AVar "") STInt STInt))
                (Var (STFun (AVar "") STBool (STFun (AVar "") STInt (STFun (AVar "") STInt STInt))) "foo")
                (bool False))
              (int 1))
            (int 1)))),
    ([], "fun fix -> fun f -> f (fun y -> fix f y)",
      Abs
        (STFun (AVar "")
          (STFun (AVar "")
            (STFun (AVar "") (STFun (AVar "") (var "x2") (var "x4")) (var "x5"))
            (STFun (AVar "") (var "x2") (var "x4")))
          (STFun (AVar "")
            (STFun (AVar "") (STFun (AVar "") (var "x2") (var "x4")) (var "x5"))
            (var "x5")))
        "fix"
        (Abs
          (STFun (AVar "")
            (STFun (AVar "") (STFun (AVar "") (var "x2") (var "x4")) (var "x5"))
            (var "x5"))
          "f"
          (App (var "x5")
            (Var (STFun (AVar "") (STFun (AVar "") (var "x2") (var "x4")) (var "x5")) "f")
            (Abs (STFun (AVar "") (var "x2") (var "x4")) "y"
              (App (var "x4")
                (App (STFun (AVar "") (var "x2") (var "x4"))
                  (Var
                    (STFun (AVar "")
                      (STFun (AVar "") (STFun (AVar "") (var "x2") (var "x4")) (var "x5"))
                      (STFun (AVar "") (var "x2") (var "x4"))) "fix")
                  (Var (STFun (AVar "") (STFun (AVar "") (var "x2") (var "x4")) (var "x5")) "f"))
                (Var (var "x2") "y")))))
      ),
    ([], "let rec fix = fun f -> f (fun y -> fix f y) in fix",
    LetRec
      (STFun (AVar "")
        (STFun (AVar "")
          (STFun (AVar "") (var "x7") (var "x6"))
          (STFun (AVar "") (var "x7") (var "x6")))
        (STFun (AVar "") (var "x7") (var "x6")))
      ("fix",
        tsForall "x4" (tsForall "x2" (tsType (STFun (AVar "")
          (STFun (AVar "")
            (STFun (AVar "") (var "x2") (var "x4"))
            (STFun (AVar "") (var "x2") (var "x4")))
          (STFun (AVar "") (var "x2") (var "x4"))))))
      ("f",
        App (STFun (AVar "") (var "x2") (var "x4"))
          (Var
            (STFun (AVar "")
              (STFun (AVar "") (var "x2") (var "x4"))
              (STFun (AVar "") (var "x2") (var "x4")))
            "f")
          (Abs (STFun (AVar "") (var "x2") (var "x4")) "y"
            (App (var "x4")
              (App (STFun (AVar "") (var "x2") (var "x4"))
                (Var
                  (STFun (AVar "")
                    (STFun (AVar "")
                      (STFun (AVar "") (var "x2") (var "x4"))
                      (STFun (AVar "") (var "x2") (var "x4")))
                    (STFun (AVar "") (var "x2") (var "x4")))
                  "fix")
                (Var
                  (STFun (AVar "")
                    (STFun (AVar "") (var "x2") (var "x4"))
                    (STFun (AVar "") (var "x2") (var "x4")))
                  "f"))
              (Var (var "x2") "y"))))
        (Var
          (STFun (AVar "")
            (STFun (AVar "")
              (STFun (AVar "") (var "x7") (var "x6"))
              (STFun (AVar "") (var "x7") (var "x6")))
            (STFun (AVar "") (var "x7") (var "x6")))
          "fix")),
    ([],
      "fun f -> f (fun x -> f (fun y -> y))",
      Abs (STFun (AVar "") (STFun (AVar "") (STFun (AVar "") (var "x4") (var "x4")) (var "x4")) (var "x4")) "f"
        (App (var "x4")
          (Var (STFun (AVar "") (STFun (AVar "") (var "x4") (var "x4")) (var "x4")) "f")
          (Abs (STFun (AVar "") (var "x4") (var "x4")) "x"
            (App (var "x4")
              (Var (STFun (AVar "") (STFun (AVar "") (var "x4") (var "x4")) (var "x4")) "f")
              (Abs (STFun (AVar "") (var "x4") (var "x4")) "y"
                (Var (var "x4") "y")))))),
    ([],
      "fun f -> f (fun x -> f (fun y -> x))",
      Abs (STFun (AVar "") (STFun (AVar "") (STFun (AVar "") (var "x4") (var "x4")) (var "x4")) (var "x4")) "f"
        (App (var "x4")
          (Var (STFun (AVar "") (STFun (AVar "") (var "x4") (var "x4")) (var "x4")) "f")
          (Abs (STFun (AVar "") (var "x4") (var "x4")) "x"
            (App (var "x4")
              (Var (STFun (AVar "") (STFun (AVar "") (var "x4") (var "x4")) (var "x4")) "f")
              (Abs (STFun (AVar "") (var "x4") (var "x4")) "y"
                (Var (var "x4") "x")))))),
    ([("x", STInt)], "x", Var STInt "x"),
    ([("f", STFun (AVar "") STInt STInt)], "f", Var (STFun (AVar "") STInt STInt) "f"),
    ([("f", STFun (AVar "") STInt STInt)], "f 3",
      App STInt (Var (STFun (AVar "") STInt STInt) "f") (int 3)),
    ([("x", var "x0")], "x - 1", OpSub STInt (Var STInt "x") (int 1)),
    ([("x", var "x0"), ("y", var "x1")], "x y",
      App (var "x2")
        (Var (STFun (AVar "") (var "x1") (var "x2")) "x")
        (Var (var "x1") "y"))
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
    ([], "fun x -> x", []),
    ([("y", STInt)], "fun x -> y", ["y"]),
    ([("y", STInt)], "fun x -> x + y", ["y"]),
    ([], "let x = 2 + 3 in x", []),
    ([], "let x = 5 in let f = fun y -> x + y in f 3", []),
    ([("sum", STFun (AVar "") STInt STInt)], "fun n -> if n = 0 then 0 else n + sum (n - 1)", ["sum"])
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

--testTypeInference :: (Context, String, Expr TypeSchema Type) -> Test
testTypeInference :: (Context, String, Expr Type Type) -> Test
testTypeInference (ctxt, prog, expr) =
  let term = Parser.parse (Lexer.alexScanTokens prog)
   in TestLabel ("program '" ++ prog ++ "' has type '" ++
        show (Expr.getType expr) ++ "'") $
        TestCase $
          case TyInferance.infer ctxt term of
            Just (subst, expr') ->
              assertEqual {-(show subst)-} "" expr expr'
            Nothing -> assertFailure "did not type checked"

testInterpreter :: (String, Value () ()) -> Test
testInterpreter (prog, val) =
  let term = Parser.parse (Lexer.alexScanTokens prog)
   in TestLabel ("program '" ++ prog ++ "' evaluate to '" ++ show val ++ "'") $
        TestCase $
          case Interpreter.eval [] term of
            Just v -> assertEqual "" val v
            Nothing -> assertFailure "evaluation went wrong"

{-
testNormalForm :: (String, String) -> Test
testNormalForm (prog, nf) =
  let term = Parser.parse (Lexer.alexScanTokens prog) in
  TestLabel prog $ TestCase $
    case TyInferance.infer [] term of
      Nothing -> assertFailure "did not type checked"
      Just (_, expr) -> assertEqual "" nf (show (Compiler.toNormalForm expr))

testFreeVariables :: (Context, String, [String]) -> Test
testFreeVariables (ctxt, prog, fvs) =
  let term = Parser.parse (Lexer.alexScanTokens prog) in
  TestLabel prog $ TestCase $
    case TyInferance.infer ctxt term of
      Nothing -> assertFailure "did not type checked"
      Just (_, expr) ->
        assertEqual "" fvs (map fst (Compiler.fv (Compiler.toNormalForm expr)))

testClosure :: (String, String) -> Test
testClosure (prog, nfc) =
  let term = Parser.parse (Lexer.alexScanTokens prog) in
  TestLabel prog $ TestCase $
    case TyInferance.infer [] term of
      Nothing -> assertFailure "did not type checked"
      Just (_, expr) ->
        let normForm = Compiler.toNormalForm expr in
        let normFormClosure = Compiler.toClosure normForm in
        assertEqual "" nfc (show normFormClosure)
-}

tests =
  TestList $ [
    TestLabel "testing (Parser.parse . Lexer.alexScanTokens)" $
      TestList (map testCompilation testCases),
    TestLabel "testing (parse prog1 == parse prog2)" $
      TestList (map testComparaison testEquivalences),
    TestLabel "testing (infer (parse prog))" $
      TestList (map testTypeInference testInference),
    TestLabel "testing (eval [] (parse prog))" $
      TestList (map testInterpreter interpretationTests){-,
    TestLabel "testing (toNormalForm (parse prog))" $
      TestList (map testNormalForm normalFormTests),
    TestLabel "Compiler.fv" $
      TestList (map testFreeVariables fvTests),
    TestLabel "Compiler.toClosure" $
      TestList (map testClosure closureTests)
    -}
  ]

main :: IO ()
main = fmap (const ()) (runTestTT tests)
