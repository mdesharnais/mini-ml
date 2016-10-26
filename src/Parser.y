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

Exp :: { Term }
Exp : AtExp                   { $1 }
    | Exp AtExp               { App $1 $2 }
    | 'fun' ID '->' Exp       { Abs $2 $4 }
    | BinOp                   { $1 }
    | Let                     { $1 }
    | If                      { $1 }

AtExp :: { Term }
AtExp : ID                    { Var $1 }
      | Lit                   { $1 }
      | '(' Exp ')'           { $2 }

Lit :: { Term }
Lit : INT                     { LitInt $1 }
    | 'true'                  { LitTrue }
    | 'false'                 { LitFalse }

BinOp :: { Term }
BinOp : AtExp '*' Exp         { OpMul $1 $3 }
      | AtExp '/' Exp         { OpDiv $1 $3 }
      | AtExp '+' Exp         { OpAdd $1 $3 }
      | AtExp '-' Exp         { OpSub $1 $3 }
      | AtExp '=' Exp         { OpEQ $1 $3 }
      | AtExp '<' Exp         { OpLT $1 $3 }

Let :: { Term }
Let : 'let' ID '=' Exp 'in' Exp         { Let $2 $4 $6 }
    | 'let' 'rec' ID '=' Exp 'in' Exp   { LetRec $3 $5 $7 }

If :: { Term }
If : 'if' Exp 'then' Exp 'else' Exp     { If $2 $4 $6 }

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
