import qualified Compiler
import qualified Data.Char
import qualified Interpreter
import qualified Lexer
import qualified Parser
import qualified Type

import Expr(Expr(..))
import Interpreter(Value(..))
import Test.HUnit
import Type(Type(..))

litBool = [
    ("true", LitBool True),
    ("false", LitBool False)
  ]

litInt min max =
  let
    impl n xs =
      if n >= max then xs else impl (n + 1) ((show n, LitInt n) : xs)
  in
    impl min []

variables = [
    ("a", Var "a"),
    ("ab", Var "ab"),
    ("ab1", Var "ab1"),
    ("ab12", Var "ab12"),
    ("ab121", Var "ab121"),
    ("ab121b", Var "ab121b"),
    ("ab121ba", Var "ab121ba")
  ]

functions = [
    ("let min = fun x -> fun y -> if x < y then x else y in min 3 5",
      Let "min"
        (Abs "x" (Abs "y" (If (OpLT (Var "x") (Var "y")) (Var "x") (Var "y"))))
        (App (App (Var "min") (LitInt 3)) (LitInt 5))),
    ("1 * 2 < 3 * 4",
      OpLT (OpMul (LitInt 1) (LitInt 2)) (OpMul (LitInt 3) (LitInt 4)))
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

testInference = [
    (Type.emptyContext, "true", TBool),
    (Type.emptyContext, "false", TBool),
    (Type.emptyContext, "1", TInt),
    (Type.emptyContext, "12", TInt),
    (Type.emptyContext, "123", TInt),
    (Type.emptyContext, "3 - 2", TInt),
    (Type.emptyContext, "3 + 2", TInt),
    (Type.emptyContext, "3 * 2", TInt),
    (Type.emptyContext, "3 / 2", TInt),
    (Type.emptyContext, "3 < 2", TBool),
    (Type.emptyContext, "3 = 2", TBool),
    (Type.emptyContext, "if true then 0 else 1", TInt),
    (Type.emptyContext, "extern f", TFun TInt TInt),
    (Type.emptyContext, "fun x -> x", TFun (TVar "x0") (TVar "x0")),
    (Type.emptyContext, "fun x -> true", TFun (TVar "x0") TBool),
    (Type.emptyContext, "let x = true in 3", TInt),
    (Type.emptyContext, "let n = 3 in fun m -> m + n", TClosure TInt TInt),
    (Type.emptyContext, "let n = 3 in fun m -> fun k -> m + n + k", TClosure TInt (TClosure TInt TInt)),
    (Type.emptyContext, "let min = fun x -> fun y -> if x < y then x else y in min 2 3", TInt),
    (Type.emptyContext, "let rec sum = fun n -> if n = 0 then 0 else n + sum (n - 1) in sum 3", TInt),
    (Type.emptyContext, "let min = fun b -> fun x -> fun y -> if b then x else y in min true 2 3", TInt),
    (Type.emptyContext, "let i = fun x -> x in if i true then i 1 else i 2", TInt),
    (Type.emptyContext, "let foo = fun b -> if b then true else false in foo true", TBool),
    (Type.emptyContext, "let rec f = fun x -> x in if f true then f 3 else f 4", TInt),
    (Type.emptyContext,
      "let not = fun b -> if b then b else false in " ++
      "let rec foo = fun b -> fun x -> fun y -> if b then x else foo (not b) y x in " ++
      "foo false 1 1", TInt),
    (Type.emptyContext, "fun fix -> fun f -> f (fun y -> fix f y)",
      TFun (TClosure (TClosure (TClosure (TVar "x2") (TVar "x4")) (TVar "x5")) (TClosure (TVar
      "x2") (TVar "x4"))) (TClosure (TClosure (TClosure (TVar "x2") (TVar "x4")) (TVar
      "x5")) (TVar "x5"))),
    (Type.emptyContext, "let rec fix = fun f -> f (fun y -> fix f y) in fix",
      TClosure (TClosure ((TVar "x8") `TClosure` (TVar "x7")) (TClosure (TVar "x8") (TVar "x7"))) (TClosure (TVar "x8") (TVar "x7"))),
    (Type.emptyContext,
      "fun f -> f (fun x -> f (fun y -> y))",
      TFun (TClosure (TFun (TVar "x4") (TVar "x4")) (TVar "x4")) (TVar "x4")),
    (Type.emptyContext,
      "fun f -> f (fun x -> f (fun y -> x))",
      TFun (TClosure (TClosure (TVar "x4") (TVar "x4")) (TVar "x4")) (TVar "x4")),
    (Type.singletonContext ("x", TInt), "x", TInt),
    (Type.singletonContext ("f", TFun TInt TInt), "f", TFun TInt TInt),
    (Type.singletonContext ("f", TFun TInt TInt), "f 3", TInt),
    (Type.singletonContext ("x", TVar "x0"), "x - 1", TInt),
    (Type.contextFromList [("x", TVar "x0"), ("y", TVar "x1")],
      "x y", TVar "x2")
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
    ("a", "a"),

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
     "let x1 = x0 True in\n" ++
     "x1"),

    ("f x y z",
     "let x0 = f x in\nlet x1 = x0 y in\nlet x2 = x1 z in\nx2"),

    ("(fun x -> x) (fun x -> x) true",
     "let x0 = (fun x -> x) in\n" ++
     "let x1 = (fun x -> x) in\n" ++
     "let x2 = x0 x1 in\n" ++
     "let x3 = x2 True in\n" ++
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

    ("if a then b else c",
     "let x0 = if a then b else c in\nx0"),

    ("if a then f 1 else f 2",
     "let x0 = if a then let x1 = f 1 in\nx1 else let x2 = f 2 in\nx2 in\nx0"),

    ("let f = fun x -> if x then 1 else 2 in f true",
     "let x0 = (fun x -> " ++
        "let x1 = if x then 1 else 2 in\n" ++
        "x1) in\n" ++
     "let x2 = x0 True in\n" ++
     "x2"),

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
    ("fun x -> x", []),
    ("fun x -> y", ["y"]),
    ("fun x -> x + y", ["y"]),
    ("let x = 2 + 3 in x", []),
    ("let x = 5 in let f = fun y -> x + y in f 3", []),
    ("fun n -> if n = 0 then 0 else n + sum (n - 1)", ["sum"])
  ]

closureTests = [
    ("let x = 5 in let f = fun y -> x + y in f 3",
     "let x0 = Closure (fun env -> fun y -> " ++
        "let x1 = 5 + y in\n" ++
        "x1, []) in\n" ++
     "let x2 = x0 3 in\n" ++
     "x2"),

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

testCompilation :: (String, Expr) -> Test
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

testTypeInference :: (Type.Context, String, Type) -> Test
testTypeInference (ctxt, prog, ty) =
  let term = Parser.parse (Lexer.alexScanTokens prog)
   in TestLabel ("program '" ++ prog ++ "' has type '" ++ show ty ++ "'") $
        TestCase $
          case Type.infer ctxt term of
            Just (subst, inferedTy) -> assertEqual (show subst) ty inferedTy
            Nothing -> assertFailure "did not type checked"

testInterpreter :: (String, Value) -> Test
testInterpreter (prog, val) =
  let term = Parser.parse (Lexer.alexScanTokens prog)
   in TestLabel ("program '" ++ prog ++ "' evaluate to '" ++ show val ++ "'") $
        TestCase $
          case Interpreter.eval [] term of
            Just v -> assertEqual "" val v
            Nothing -> assertFailure "evaluation went wrong"

testNormalForm :: (String, String) -> Test
testNormalForm (prog, nf) =
  let term = Parser.parse (Lexer.alexScanTokens prog)
      normForm = Compiler.toNormalForm term
   in TestLabel prog $
        TestCase $ assertEqual "" nf (show normForm)

testFreeVariables :: (String, [String]) -> Test
testFreeVariables (prog, fvs) =
  let term = Parser.parse (Lexer.alexScanTokens prog)
      normForm = Compiler.toNormalForm term
   in TestLabel (show normForm) $
        TestCase $ assertEqual "" fvs (Compiler.fv normForm)

testClosure :: (String, String) -> Test
testClosure (prog, nfc) =
  let term = Parser.parse (Lexer.alexScanTokens prog)
      normForm = Compiler.toNormalForm term
      normFormClosure = Compiler.toClosure normForm
   in TestLabel (show normForm) $
        TestCase $ assertEqual "" nfc (show normFormClosure)

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
