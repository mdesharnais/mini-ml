{
module Lexer where
}

%wrapper "posn"

$digit = 0-9
$alpha = [a-zA-Z]
$alnum = [ $alpha $digit ]


tokens :-

  $white+           ;
  "true"            { \p s -> (p, TLitTrue) }
  "false"           { \p s -> (p, TLitFalse) }
  "->"              { \p s -> (p, TArrow) }
  "*"               { \p s -> (p, TMul) }
  "/"               { \p s -> (p, TDiv) }
  "+"               { \p s -> (p, TAdd) }
  "-"               { \p s -> (p, TSub) }
  "<"               { \p s -> (p, TLe) }
  "="               { \p s -> (p, TEq) }
  "("               { \p s -> (p, TLPar) }
  ")"               { \p s -> (p, TRPar) }
  "fun"             { \p s -> (p, TFun) }
  "if"              { \p s -> (p, TIf) }
  "then"            { \p s -> (p, TThen) }
  "else"            { \p s -> (p, TElse) }
  "let"             { \p s -> (p, TLet) }
  "in"              { \p s -> (p, TIn) }
  "rec"             { \p s -> (p, TRec) }
  "extern"          { \p s -> (p, TExtern) }
  $digit+           { \p s -> (p, TLitInt (read s)) }
  $alpha $alnum*    { \p s -> (p, TId s) }

{
data Tok =
  TLitInt Integer |
  TLitTrue |
  TLitFalse |
  TId String |
  TArrow |
  TMul |
  TDiv |
  TAdd |
  TSub |
  TLe |
  TEq |
  TLPar |
  TRPar |
  TFun |
  TIf |
  TThen |
  TElse |
  TLet |
  TIn |
  TRec |
  TExtern
  deriving (Eq,Show)

type Token = (AlexPosn, Tok)

getPosition :: Token -> AlexPosn
getPosition = fst
}
