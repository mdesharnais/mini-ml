module FreeVars where

class FreeVars a where
  freeVars :: a -> [String]
