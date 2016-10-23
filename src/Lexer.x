{
module Lexer where
}

%wrapper "posn"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-

  $white+       ;
  "true"        { \p s -> LitBool p True}
  "false"       { \p s -> LitBool p False}
  "->"          { \p s -> Arrow p }
  "*"           { \p s -> Mul p }
  "/"           { \p s -> Div p }
  "+"           { \p s -> Add p }
  "-"           { \p s -> Sub p }
  "<"           { \p s -> Le p }
  "="           { \p s -> Eq p }
  "("           { \p s -> LPar p }
  ")"           { \p s -> RPar p }
  "fun"         { \p s -> Fun p }
  "if"          { \p s -> If p }
  "then"        { \p s -> Then p }
  "else"        { \p s -> Else p }
  "let"         { \p s -> Let p }
  "in"          { \p s -> In p }
  "rec"         { \p s -> Rec p }
  $digit+       { \p s -> LitInt p (read s) }
  $alpha+       { \p s -> Id p s }

{
data Token =
  LitInt AlexPosn Integer |
  LitBool AlexPosn Bool |
  Id AlexPosn String |
  Arrow AlexPosn |
  Mul AlexPosn |
  Div AlexPosn |
  Add AlexPosn |
  Sub AlexPosn |
  Le AlexPosn |
  Eq AlexPosn |
  LPar AlexPosn |
  RPar AlexPosn |
  Fun AlexPosn |
  If AlexPosn |
  Then AlexPosn |
  Else AlexPosn |
  Let AlexPosn |
  In AlexPosn |
  Rec AlexPosn
  deriving (Eq,Show)
}
