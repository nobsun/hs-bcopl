module Language.BCoPL.DataLevel.Exp (
    -- * Types
    Exp(..)
  , operator
  , loperand
  , roperand
  ) where

import Text.ParserCombinators.ReadP
import Language.BCoPL.DataLevel.Peano(Nat(..))

data Exp = Nat Nat
         | Exp :+: Exp
         | Exp :*: Exp
         deriving (Eq)

operator :: Exp -> (Exp -> Exp -> Exp)
operator (_ :+: _) = (:+:)
operator (_ :*: _) = (:*:)

loperand :: Exp -> Exp
loperand (l :+: _) = l
loperand (l :*: _) = l

roperand :: Exp -> Exp
roperand (_ :+: r) = r
roperand (_ :*: r) = r

instance Show Exp where
  show e = case e of
    Nat n     -> show n
    e1 :+: e2 -> show e1 ++ " + " ++ show e2
    e1 :*: e2 -> show' e1 ++ " * " ++ show' e2
    where
      show' e' = case e' of
        e1' :+: e2' -> "("++show e'++")"
        _           -> show e'

instance Read Exp where
  readsPrec _ = readP_to_S expr

expr :: ReadP Exp
expr    = term   `chainl1` addop
term    = factor `chainl1` mulop
factor  = parens expr +++ nat

mulop   = do { skipSpaces
             ; string "*"
             ; skipSpaces
             ; return (:*:)
             }
addop   = do { skipSpaces
             ; string "+"
             ; skipSpaces
             ; return (:+:)
             }

nat :: ReadP Exp
nat = peano >>= return . Nat

peano :: ReadP Nat
peano = readS_to_P (readsPrec 0)

parens :: ReadP a -> ReadP a
parens p =  do { skipSpaces 
               ; char '('
               ; skipSpaces
               ; c <- p
               ; skipSpaces
               ; char ')'
               ; return c
               }
