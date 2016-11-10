import qualified Interpreter
import qualified Lexer
import qualified Parser
import qualified Type
import qualified Data.Char

import Interpreter(Value, valInt, valBool)
import Parser(Term(..))
import Test.HUnit
import Type(Type(..))

litBool = [
  ("true", LitTrue),
  ("false", LitFalse)
  ]

litInt min max =
  let
    impl n xs =
      if n >= max then xs else impl (n + 1) ((show n, LitInt n) : xs)
  in
    impl min []

variables =
  let
    {-
    kleene :: [String] -> [String] -> [String]
    kleene v vi =
      let vii = [ x ++ y | x <- vi, y <- v ]
       in vi ++ kleene v vii

    kleeneStar sigma = kleene (map (:[]) sigma) [""]
    kleenePlus sigma = let xs = map (:[]) sigma in kleene xs xs

    sigma = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    vars = takeWhile ((<= 2) . length) (kleenePlus sigma)
    mkTest var = (var, Var var)
  in
    map mkTest vars
  -}
  in [
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
        (App (App (Var "min") (LitInt 3)) (LitInt 5)))
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
    (Type.emptyContext, "fun x -> x", TFun (TVar "x0") (TVar "x0")),
    (Type.emptyContext, "fun x -> true", TFun (TVar "x0") TBool),
    (Type.emptyContext, "let x = true in 3", TInt),
    (Type.emptyContext, "let min = fun x -> fun y -> if x < y then x else y in min 2 3", TInt),
    (Type.emptyContext, "let rec sum = fun n -> if n = 0 then 0 else n + sum (n - 1) in sum 3", TInt),
    (Type.emptyContext, "let min = fun b -> fun x -> fun y -> if b then x else y in min true 2 3", TInt),
    (Type.emptyContext, "let i = fun x -> x in if i true then i 1 else i 2", TInt),
    (Type.emptyContext, "let foo = fun b -> if b then true else false in foo true", TBool),
    (Type.emptyContext,
      "let not = fun b -> if b then b else false in " ++
      "let rec foo = fun b -> fun x -> fun y -> if b then x else foo (not b) y x in " ++
      "foo false 1 1", TInt),
    (Type.emptyContext, "fun fix -> fun f -> f (fun y -> fix f y)",
      TFun (TFun (TFun (TFun (TVar "x2") (TVar "x4")) (TVar "x5")) (TFun (TVar
      "x2") (TVar "x4"))) (TFun (TFun (TFun (TVar "x2") (TVar "x4")) (TVar
      "x5")) (TVar "x5"))),
    (Type.emptyContext, "let rec fix = fun f -> f (fun y -> fix f y) in fix",
      TFun (TFun ((TVar "x2") `TFun` (TVar "x4")) (TFun (TVar "x2") (TVar "x4"))) (TFun (TVar "x2") (TVar "x4"))),
    (Type.emptyContext,
      "fun f -> f (fun x -> f (fun y -> y))",
      TFun (TFun (TFun (TVar "x4") (TVar "x4")) (TVar "x4")) (TVar "x4")),
    (Type.emptyContext,
      "fun f -> f (fun x -> f (fun y -> x))",
      TFun (TFun (TFun (TVar "x4") (TVar "x4")) (TVar "x4")) (TVar "x4")),
    (Type.singletonContext ("x", TInt), "x", TInt),
    (Type.singletonContext ("f", TFun TInt TInt), "f", TFun TInt TInt),
    (Type.singletonContext ("f", TFun TInt TInt), "f 3", TInt),
    (Type.singletonContext ("x", TVar "x0"), "x - 1", TInt),
    (Type.contextFromList [("x", TVar "x0"), ("y", TVar "x1")],
      "x y", TVar "x2")
  ]

interpretationTests = [
    ("4 + 2", valInt 6),
    ("4 - 2", valInt 2),
    ("4 * 2", valInt 8),
    ("4 / 2", valInt 2),
    ("6 + 4 / 2", valInt 8),
    ("2 * 3 + 4 / 2", valInt 8),
    ("2 < 4", valBool True),
    ("4 < 2", valBool False),
    ("let f = fun x -> x in f 0", valInt 0),
    ("let i = fun x -> x in if i true then i 1 else i 2", valInt 1),
    ("let rec sum = fun n -> if n = 0 then 0 else n + sum (n - 1) in sum 3", valInt 6)
  ]

testCompilation :: (String, Term) -> Test
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

tests =
  TestList $ [
    TestLabel "testing (Parser.parse . Lexer.alexScanTokens)" $
      TestList (map testCompilation testCases),
    TestLabel "testing (parse prog1 == parse prog2)" $
      TestList (map testComparaison testEquivalences),
    TestLabel "testing (infer (parse prog))" $
      TestList (map testTypeInference testInference),
    TestLabel "testing (eval [] (parse prog))" $
      TestList (map testInterpreter interpretationTests)
  ]

main :: IO ()
main = fmap (const ()) (runTestTT tests)
