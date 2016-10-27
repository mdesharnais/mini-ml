{
module Parser where

import Lexer
}

%name parse
%tokentype { Token }

%token
  'true'        { (_, TLitTrue) }
  'false'       { (_, TLitFalse) }
  '->'          { (_, TArrow) }
  '*'           { (_, TMul) }
  '/'           { (_, TDiv) }
  '+'           { (_, TAdd) }
  '-'           { (_, TSub) }
  '<'           { (_, TLe) }
  '='           { (_, TEq) }
  '('           { (_, TLPar) }
  ')'           { (_, TRPar) }
  'fun'         { (_, TFun) }
  'if'          { (_, TIf) }
  'then'        { (_, TThen) }
  'else'        { (_, TElse) }
  'let'         { (_, TLet) }
  'in'          { (_, TIn) }
  'rec'         { (_, TRec) }
  INT           { (_, TLitInt $$) }
  ID            { (_, TId $$) }

%left '+' '-'
%left '*' '/'
%nonassoc '<' '='
%%

Exp :: { Term }
Exp : Abs                     { $1 }
    | Exp0                    { $1 }
    | If                      { $1 }
    | Let                     { $1 }

Exp0 :: { Term }
Exp0 : ArithExp               { $1 }
     | App                    { $1 }

Abs :: { Term }
Abs : 'fun' ID '->' Exp       { Abs $2 $4 }

App :: { Term }
App : App AtExp               { App $1 $2 }
    | AtExp                   { $1 }

AtExp :: { Term }
AtExp : ID                    { Var $1 }
      | Lit                   { $1 }
      | '(' Exp ')'           { $2 }

Lit :: { Term }
Lit : INT                     { LitInt $1 }
    | 'true'                  { LitTrue }
    | 'false'                 { LitFalse }

ArithExp :: { Term }
ArithExp : Exp0 '+' Exp0      { OpAdd $1 $3 }
         | Exp0 '-' Exp0      { OpSub $1 $3 }
         | Exp0 '*' Exp0      { OpMul $1 $3 }
         | Exp0 '/' Exp0      { OpDiv $1 $3 }
         | Exp0 '<' Exp0      { OpLT $1 $3 }
         | Exp0 '=' Exp0      { OpEQ $1 $3 }

Let :: { Term }
Let : 'let' ID '=' Exp 'in' Exp         { Let $2 $4 $6 }
    | 'let' 'rec' ID '=' Abs 'in' Exp   { LetRec $3 $5 $7 }

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
