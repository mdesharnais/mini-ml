{
module Lexer where
}

%wrapper "posn"

$digit = 0-9
$alpha = [a-zA-Z]
$alnum = [ $alpha $digit ]


tokens :-

  $white+           ;
  "true"            { \p s -> TLitTrue p }
  "false"           { \p s -> TLitFalse p }
  "->"              { \p s -> TArrow p }
  "*"               { \p s -> TMul p }
  "/"               { \p s -> TDiv p }
  "+"               { \p s -> TAdd p }
  "-"               { \p s -> TSub p }
  "<"               { \p s -> TLe p }
  "="               { \p s -> TEq p }
  "("               { \p s -> TLPar p }
  ")"               { \p s -> TRPar p }
  "fun"             { \p s -> TFun p }
  "if"              { \p s -> TIf p }
  "then"            { \p s -> TThen p }
  "else"            { \p s -> TElse p }
  "let"             { \p s -> TLet p }
  "in"              { \p s -> TIn p }
  "rec"             { \p s -> TRec p }
  $digit+           { \p s -> TLitInt p (read s) }
  $alpha $alnum*    { \p s -> TId p s }

{
data Token =
  TLitInt AlexPosn Integer |
  TLitTrue AlexPosn |
  TLitFalse AlexPosn |
  TId AlexPosn String |
  TArrow AlexPosn |
  TMul AlexPosn |
  TDiv AlexPosn |
  TAdd AlexPosn |
  TSub AlexPosn |
  TLe AlexPosn |
  TEq AlexPosn |
  TLPar AlexPosn |
  TRPar AlexPosn |
  TFun AlexPosn |
  TIf AlexPosn |
  TThen AlexPosn |
  TElse AlexPosn |
  TLet AlexPosn |
  TIn AlexPosn |
  TRec AlexPosn
  deriving (Eq,Show)

getPosition :: Token -> AlexPosn
getPosition (TLitInt p _) = p
getPosition (TLitTrue p) = p
getPosition (TLitFalse p) = p
getPosition (TId p _) = p
getPosition (TArrow p) = p
getPosition (TMul p) = p
getPosition (TDiv p) = p
getPosition (TAdd p) = p
getPosition (TSub p) = p
getPosition (TLe p) = p
getPosition (TEq p) = p
getPosition (TLPar p) = p
getPosition (TRPar p) = p
getPosition (TFun p) = p
getPosition (TIf p) = p
getPosition (TThen p) = p
getPosition (TElse p) = p
getPosition (TLet p) = p
getPosition (TIn p) = p
getPosition (TRec p) = p
}
