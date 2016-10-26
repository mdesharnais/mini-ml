{
module Parser where

import Lexer
}

%name parse
%tokentype { Token }

%token
  'true'        { TLitTrue _ }
  'false'       { TLitFalse _ }
  '->'          { TArrow _ }
  '*'           { TMul _ }
  '/'           { TDiv _ }
  '+'           { TAdd _ }
  '-'           { TSub _ }
  '<'           { TLe _ }
  '='           { TEq _ }
  '('           { TLPar _ }
  ')'           { TRPar _ }
  'fun'         { TFun _ }
  'if'          { TIf _ }
  'then'        { TThen _ }
  'else'        { TElse _ }
  'let'         { TLet _ }
  'in'          { TIn _ }
  'rec'         { TRec _ }
  INT           { TLitInt _ $$ }
  ID            { TId _ $$ }

%nonassoc '<' '='
%left '+' '-'
%left '*' '/'

%%

Term :: { Term }
Term : Abs                    { $1 }
     | App                    { $1 }
     | Lit                    { $1 }
     | BinOp                  { $1 }
     | IfThenElse             { $1 }
     | Let                    { $1 }

Abs :: { Term }
Abs : 'fun' ID '->' Term      { Abs $2 $4 }

App :: { Term }
App : AtomicExpr              { $1 }
    | App AtomicExpr          { App $1 $2 }

AtomicExpr :: { Term }
AtomicExpr : ID               { Var $1 }
           | '(' Term ')'     { $2 }

Lit :: { Term }
Lit : INT                     { LitInt $1 }
    | 'true'                  { LitTrue }
    | 'false'                 { LitFalse }

BinOp :: { Term }
BinOp : Term '*' Term         { OpMul $1 $3 }
      | Term '/' Term         { OpDiv $1 $3 }
      | Term '+' Term         { OpAdd $1 $3 }
      | Term '-' Term         { OpSub $1 $3 }
      | Term '=' Term         { OpEQ $1 $3 }
      | Term '<' Term         { OpLT $1 $3 }

IfThenElse :: { Term }
IfThenElse : 'if' Term 'then' Term 'else' Term    { If $2 $4 $6 }

Let :: { Term }
Let : 'let' ID '=' Term 'in' Term                 { Let $2 $4 $6 }
    | 'let' 'rec' ID '=' Term 'in' Term           { LetRec $3 $5 $7 }

{
data Term =
  Var String |
  Abs String Term |
  App Term Term |
  LitInt Integer |
  LitTrue |
  LitFalse |
  OpMul Term Term |
  OpDiv Term Term |
  OpAdd Term Term |
  OpSub Term Term |
  OpLT Term Term |
  OpEQ Term Term |
  If Term Term Term |
  Let String Term Term |
  LetRec String Term Term
  deriving (Eq,Show)

happyError :: [Token] -> a
happyError ts = error ("Parse error at " ++ lcn ++ "\n")
  where
  lcn =   case ts of
      [] -> "end of file"
      (t:_) -> "line " ++ show l ++ ", column " ++ show c ++ " (token " ++ (show t) ++ ")"
        where AlexPn _ l c = getPosition t

}
