import qualified Lexer
import qualified Parser
import qualified Type
import qualified Data.Char

import Parser(Term(..))
import Type(Type(..))
import Test.HUnit

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
    (Type.singletonContext ("x", TInt), "x", TInt),
    (Type.singletonContext ("f", TFun TInt TInt), "f", TFun TInt TInt),
    (Type.singletonContext ("f", TFun TInt TInt), "f 3", TInt),
    (Type.singletonContext ("x", TVar "x0"), "x - 1", TInt),
    (Type.contextFromList [("x", TVar "x0"), ("y", TVar "x1")],
      "x y", TVar "x2")
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

tests =
  TestList $ [
    TestLabel "testing (Parser.parse . Lexer.alexScanTokens)" $
      TestList (map testCompilation testCases),
    TestLabel "testing (parse prog1 == parse prog2)" $
      TestList (map testComparaison testEquivalences),
    TestLabel "testing (infer (parse prog))" $
      TestList (map testTypeInference testInference)
  ]

main :: IO ()
main = fmap (const ()) (runTestTT tests)
