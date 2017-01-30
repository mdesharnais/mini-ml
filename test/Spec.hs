import qualified Compiler
import qualified Data.Char
import qualified Expr
import qualified Interpreter
import qualified Lexer
import qualified Parser
import qualified Type

import Expr(Expr(..))
import Interpreter(Value(..))
import Test.HUnit
import Type(Type(..), TypeSchema(..))

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

testInference :: [(Type.Context, String, Expr TypeSchema Type)]
testInference =
  let int = LitInt TInt in
  let bool = LitBool TBool in [
    (Type.emptyContext, "true", bool True),
    (Type.emptyContext, "false", bool False),
    (Type.emptyContext, "1", int 1),
    (Type.emptyContext, "12", int 12),
    (Type.emptyContext, "123", int 123),
    (Type.emptyContext, "3 - 2", OpSub TInt (int 3) (int 2)),
    (Type.emptyContext, "3 + 2", OpAdd TInt (int 3) (int 2)),
    (Type.emptyContext, "3 * 2", OpMul TInt (int 3) (int 2)),
    (Type.emptyContext, "3 / 2", OpDiv TInt (int 3) (int 2)),
    (Type.emptyContext, "3 < 2", OpLT TBool (int 3) (int 2)),
    (Type.emptyContext, "3 = 2", OpEQ TBool (int 3) (int 2)),
    (Type.emptyContext, "if true then 0 else 1",
      If TInt (bool True) (int 0) (int 1)),
    (Type.emptyContext, "extern f",
      ExternVar (TFun TInt TInt) "f"),
    (Type.emptyContext, "fun x -> x",
      Abs (TFun (TVar "x0") (TVar "x0")) "x" (Var (TVar "x0") "x")),
    (Type.emptyContext, "fun x -> true",
      Abs (TFun (TVar "x0") TBool) "x" (bool True)),
    (Type.emptyContext, "let x = true in 3",
      Let TInt ("x", TSType TBool) (bool True) (int 3)),
    (Type.emptyContext, "let min = fun x -> fun y -> if x < y then x else y in min 2 3",
      Let TInt ("min", (TSType (TFun TInt (TFun TInt TInt))))
        (Abs (TFun TInt (TFun TInt TInt)) "x"
          (Abs (TFun TInt TInt) "y"
            (If TInt (OpLT TBool (Var TInt "x") (Var TInt "y"))
              (Var TInt "x")
              (Var TInt "y"))))
        (App TInt
          (App (TFun TInt TInt)
            (Var (TFun TInt (TFun TInt TInt)) "min")
            (int 2))
          (int 3))),
    (Type.emptyContext, "let rec sum = fun n -> if n = 0 then 0 else n + sum (n - 1) in sum 3",
      LetRec TInt ("sum", TSType (TFun TInt TInt))
        ("n",
          (If TInt (OpEQ TBool (Var TInt "n") (int 0))
            (int 0)
            (OpAdd TInt
              (Var TInt "n")
              (App TInt
                (Var (TFun TInt TInt) "sum")
                (OpSub TInt (Var TInt "n") (int 1))))))
        (App TInt (Var (TFun TInt TInt) "sum") (int 3))),
    (Type.emptyContext, "let f = fun x -> fun y -> if true then x else y in f 2 3",
      Let TInt ("f", TSForall "x1" (TSType (TFun (TVar "x1") (TFun (TVar "x1") (TVar "x1")))))
        (Abs (TFun (TVar "x1") (TFun (TVar "x1") (TVar "x1"))) "x"
          (Abs (TFun (TVar "x1") (TVar "x1")) "y"
            (If (TVar "x1") (bool True)
              (Var (TVar "x1") "x")
              (Var (TVar "x1") "y"))))
          (App TInt
            (App (TFun TInt TInt)
              (Var (TFun TInt (TFun TInt TInt)) "f")
              (int 2))
          (int 3))),
    (Type.emptyContext, "let f = fun b -> fun x -> fun y -> if b then x else y in f true 2 3",
      Let TInt ("f", (TSForall "x2" (TSType
          (TFun TBool (TFun (TVar "x2") (TFun (TVar "x2") (TVar "x2")))))))
        (Abs (TFun TBool (TFun (TVar "x2") (TFun (TVar "x2") (TVar "x2")))) "b"
          (Abs (TFun (TVar "x2") (TFun (TVar "x2") (TVar "x2"))) "x"
            (Abs (TFun (TVar "x2") (TVar "x2")) "y"
              (If (TVar "x2") (Var TBool "b")
                (Var (TVar "x2") "x")
                (Var (TVar "x2") "y")))))
        (App TInt
          (App (TFun TInt TInt)
            (App (TFun TInt (TFun TInt TInt))
              (Var (TFun TBool (TFun TInt (TFun TInt TInt))) "f")
              (bool True))
            (int 2))
          (int 3))),
    (Type.emptyContext, "let i = fun x -> x in if i true then i 1 else i 2",
      Let TInt ("i", TSForall "x0" (TSType (TFun (TVar "x0") (TVar "x0"))))
        (Abs (TFun (TVar "x0") (TVar "x0")) "x"
          (Var (TVar "x0") "x"))
        (If TInt (App TBool (Var (TFun TBool TBool) "i") (bool True))
          (App TInt (Var (TFun TInt TInt) "i") (int 1))
          (App TInt (Var (TFun TInt TInt) "i") (int 2)))),
    (Type.emptyContext, "let foo = fun b -> if b then true else false in foo true",
      Let TBool ("foo", (TSType (TFun TBool TBool)))
        (Abs (TFun TBool TBool) "b"
          (If TBool (Var TBool "b")
            (bool True)
            (bool False)))
        (App TBool (Var (TFun TBool TBool) "foo") (bool True))),
    (Type.emptyContext, "let rec f = fun x -> x in if f true then f 3 else f 4",
      (LetRec TInt ("f", TSForall "x1" (TSType (TFun (TVar "x1") (TVar "x1"))))
        ("x", (Var (TVar "x1")) "x")
        (If TInt (App TBool (Var (TFun TBool TBool) "f") (bool True))
          (App TInt (Var (TFun TInt TInt) "f") (int 3))
          (App TInt (Var (TFun TInt TInt) "f") (int 4))))),
    (Type.emptyContext,
      "let not = fun b -> if b then b else false in " ++
      "let rec foo = fun b -> fun x -> fun y -> " ++
        "if b then x else foo (not b) y x in " ++
      "foo false 1 1",
        Let TInt ("not", TSType (TFun TBool TBool))
          (Abs (TFun TBool TBool) "b"
            (If TBool (Var TBool "b")
              (Var TBool "b")
              (bool False)))
        (LetRec TInt ("foo", TSForall "x8" (TSType
          (TFun TBool (TFun (TVar "x8") (TFun (TVar "x8") (TVar "x8"))))))
          ("b", Abs (TFun (TVar "x8") (TFun (TVar "x8") (TVar "x8"))) "x"
            (Abs (TFun (TVar "x8") (TVar "x8")) "y"
              (If (TVar "x8") (Var TBool "b")
                (Var (TVar "x8") "x")
                (App (TVar "x8")
                  (App (TFun (TVar "x8") (TVar "x8"))
                    (App (TFun (TVar "x8") (TFun (TVar "x8") (TVar "x8")))
                      (Var (TFun TBool (TFun (TVar "x8")
                        (TFun (TVar "x8") (TVar "x8")))) "foo")
                      (App TBool
                        (Var (TFun TBool TBool) "not")
                        (Var TBool "b")))
                    (Var (TVar "x8") "y"))
                  (Var (TVar "x8") "x")))))
          (App TInt
            (App (TFun TInt TInt)
              (App (TFun TInt (TFun TInt TInt))
                (Var (TFun TBool (TFun TInt (TFun TInt TInt))) "foo")
                (bool False))
              (int 1))
            (int 1)))),
    (Type.emptyContext, "fun fix -> fun f -> f (fun y -> fix f y)",
      Abs
        (TFun
          (TFun
            (TFun (TFun (TVar "x2") (TVar "x4")) (TVar "x5"))
            (TFun (TVar "x2") (TVar "x4")))
          (TFun
            (TFun (TFun (TVar "x2") (TVar "x4")) (TVar "x5"))
            (TVar "x5")))
        "fix"
        (Abs
          (TFun
            (TFun (TFun (TVar "x2") (TVar "x4")) (TVar "x5"))
            (TVar "x5"))
          "f"
          (App (TVar "x5")
            (Var (TFun (TFun (TVar "x2") (TVar "x4")) (TVar "x5")) "f")
            (Abs (TFun (TVar "x2") (TVar "x4")) "y"
              (App (TVar "x4")
                (App (TFun (TVar "x2") (TVar "x4"))
                  (Var
                    (TFun
                      (TFun (TFun (TVar "x2") (TVar "x4")) (TVar "x5"))
                      (TFun (TVar "x2") (TVar "x4"))) "fix")
                  (Var (TFun (TFun (TVar "x2") (TVar "x4")) (TVar "x5")) "f"))
                (Var (TVar "x2") "y")))))
      ),
    (Type.emptyContext, "let rec fix = fun f -> f (fun y -> fix f y) in fix",
    LetRec
      (TFun
        (TFun
          (TFun (TVar "x7") (TVar "x6"))
          (TFun (TVar "x7") (TVar "x6")))
        (TFun (TVar "x7") (TVar "x6")))
      ("fix",
        TSForall "x4" (TSForall "x2" (TSType (TFun
          (TFun
            (TFun (TVar "x2") (TVar "x4"))
            (TFun (TVar "x2") (TVar "x4")))
          (TFun (TVar "x2") (TVar "x4"))))))
      ("f",
        App (TFun (TVar "x2") (TVar "x4"))
          (Var
            (TFun
              (TFun (TVar "x2") (TVar "x4"))
              (TFun (TVar "x2") (TVar "x4")))
            "f")
          (Abs (TFun (TVar "x2") (TVar "x4")) "y"
            (App (TVar "x4")
              (App (TFun (TVar "x2") (TVar "x4"))
                (Var
                  (TFun
                    (TFun
                      (TFun (TVar "x2") (TVar "x4"))
                      (TFun (TVar "x2") (TVar "x4")))
                    (TFun (TVar "x2") (TVar "x4")))
                  "fix")
                (Var
                  (TFun
                    (TFun (TVar "x2") (TVar "x4"))
                    (TFun (TVar "x2") (TVar "x4")))
                  "f"))
              (Var (TVar "x2") "y"))))
        (Var
          (TFun
            (TFun
              (TFun (TVar "x7") (TVar "x6"))
              (TFun (TVar "x7") (TVar "x6")))
            (TFun (TVar "x7") (TVar "x6")))
          "fix")),
    (Type.emptyContext,
      "fun f -> f (fun x -> f (fun y -> y))",
      Abs (TFun (TFun (TFun (TVar "x4") (TVar "x4")) (TVar "x4")) (TVar "x4")) "f"
        (App (TVar "x4")
          (Var (TFun (TFun (TVar "x4") (TVar "x4")) (TVar "x4")) "f")
          (Abs (TFun (TVar "x4") (TVar "x4")) "x"
            (App (TVar "x4")
              (Var (TFun (TFun (TVar "x4") (TVar "x4")) (TVar "x4")) "f")
              (Abs (TFun (TVar "x4") (TVar "x4")) "y"
                (Var (TVar "x4") "y")))))),
    (Type.emptyContext,
      "fun f -> f (fun x -> f (fun y -> x))",
      Abs (TFun (TFun (TFun (TVar "x4") (TVar "x4")) (TVar "x4")) (TVar "x4")) "f"
        (App (TVar "x4")
          (Var (TFun (TFun (TVar "x4") (TVar "x4")) (TVar "x4")) "f")
          (Abs (TFun (TVar "x4") (TVar "x4")) "x"
            (App (TVar "x4")
              (Var (TFun (TFun (TVar "x4") (TVar "x4")) (TVar "x4")) "f")
              (Abs (TFun (TVar "x4") (TVar "x4")) "y"
                (Var (TVar "x4") "x")))))),
    (Type.singletonContext ("x", TInt), "x",
      Var TInt "x"),
    (Type.singletonContext ("f", TFun TInt TInt), "f",
      Var (TFun TInt TInt) "f"),
    (Type.singletonContext ("f", TFun TInt TInt), "f 3",
      App TInt (Var (TFun TInt TInt) "f") (int 3)),
    (Type.singletonContext ("x", TVar "x0"), "x - 1",
      OpSub TInt (Var TInt "x") (int 1)),
    (Type.contextFromList [("x", TVar "x0"), ("y", TVar "x1")], "x y",
      App (TVar "x2")
        (Var (TFun (TVar "x1") (TVar "x2")) "x")
        (Var (TVar "x1") "y"))
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
    (Type.emptyContext, "fun x -> x", []),
    (Type.singletonContext ("y", TInt), "fun x -> y", ["y"]),
    (Type.singletonContext ("y", TInt), "fun x -> x + y", ["y"]),
    (Type.emptyContext, "let x = 2 + 3 in x", []),
    (Type.emptyContext, "let x = 5 in let f = fun y -> x + y in f 3", []),
    (Type.singletonContext ("sum", TFun TInt TInt), "fun n -> if n = 0 then 0 else n + sum (n - 1)", ["sum"])
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

testTypeInference :: (Type.Context, String, Expr TypeSchema Type) -> Test
testTypeInference (ctxt, prog, expr) =
  let term = Parser.parse (Lexer.alexScanTokens prog)
   in TestLabel ("program '" ++ prog ++ "' has type '" ++
        show (Expr.getType expr) ++ "'") $
        TestCase $
          case Type.infer ctxt term of
            Just (subst, expr') ->
              assertEqual (show subst) expr expr'
            Nothing -> assertFailure "did not type checked"

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
    case Type.infer Type.emptyContext term of
      Nothing -> assertFailure "did not type checked"
      Just (_, expr) -> assertEqual "" nf (show (Compiler.toNormalForm expr))

testFreeVariables :: (Type.Context, String, [String]) -> Test
testFreeVariables (ctxt, prog, fvs) =
  let term = Parser.parse (Lexer.alexScanTokens prog) in
  TestLabel prog $ TestCase $
    case Type.infer ctxt term of
      Nothing -> assertFailure "did not type checked"
      Just (_, expr) ->
        assertEqual "" fvs (map fst (Compiler.fv (Compiler.toNormalForm expr)))

testClosure :: (String, String) -> Test
testClosure (prog, nfc) =
  let term = Parser.parse (Lexer.alexScanTokens prog) in
  TestLabel prog $ TestCase $
    case Type.infer Type.emptyContext term of
      Nothing -> assertFailure "did not type checked"
      Just (_, expr) ->
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
