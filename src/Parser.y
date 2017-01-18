{
module Parser where

import Expr(Expr(..))
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
  'extern'      { (_, TExtern) }
  INT           { (_, TLitInt $$) }
  ID            { (_, TId $$) }

%nonassoc '<' '='
%left '+' '-'
%left '*' '/'
%%

Exp :: { Expr () () }
Exp : Abs                     { $1 }
    | Exp0                    { $1 }
    | If                      { $1 }
    | Let                     { $1 }

Exp0 :: { Expr () () }
Exp0 : ArithExp               { $1 }
     | App                    { $1 }

Abs :: { Expr () () }
Abs : 'fun' ID '->' Exp       { Abs () $2 $4 }

App :: { Expr () () }
App : App AtExp               { App () $1 $2 }
    | AtExp                   { $1 }

AtExp :: { Expr () () }
AtExp : ID                    { Var () $1 }
      | Lit                   { $1 }
      | ExternId              { $1 }
      | '(' Exp ')'           { $2 }

Lit :: { Expr () () }
Lit : INT                     { LitInt () $1 }
    | 'true'                  { LitBool () True }
    | 'false'                 { LitBool () False }

ArithExp :: { Expr () () }
ArithExp : Exp0 '+' Exp0      { OpAdd () $1 $3 }
         | Exp0 '-' Exp0      { OpSub () $1 $3 }
         | Exp0 '*' Exp0      { OpMul () $1 $3 }
         | Exp0 '/' Exp0      { OpDiv () $1 $3 }
         | Exp0 '<' Exp0      { OpLT  () $1 $3 }
         | Exp0 '=' Exp0      { OpEQ  () $1 $3 }

Let :: { Expr () () }
Let : 'let' ID '=' Exp 'in' Exp                        { Let () ($2, ()) $4 $6 }
    | 'let' 'rec' ID '=' 'fun' ID '->' Exp 'in' Exp    { LetRec () ($3, ()) ($6, $8) $10 }

If :: { Expr () () }
If : 'if' Exp 'then' Exp 'else' Exp     { If () $2 $4 $6 }

ExternId :: { Expr () () }
ExternId : 'extern' ID        { ExternVar () $2 }

{
happyError :: [Token] -> a
happyError ts = error ("Parse error at " ++ lcn ++ "\n")
  where
  lcn =   case ts of
      [] -> "end of file"
      (t:_) -> "line " ++ show l ++ ", column " ++ show c ++ " (token " ++ (show t) ++ ")"
        where AlexPn _ l c = getPosition t

}
