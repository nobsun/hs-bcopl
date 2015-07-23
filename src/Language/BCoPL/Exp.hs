{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.BCoPL.Exp where

import Text.ParserCombinators.ReadP
import Language.BCoPL.Peano

data Exp = ENat Nat
         | Exp :+ Exp
         | Exp :* Exp

instance Show Exp where
  show (ENat n) = show n
  show (e1 :+ e2) = show e1 ++ " + " ++ show e2
  show (e1 :* e2) = show' e1 ++ " * " ++ show' e2
    where
      show' e@(_ :+ _) = "("++show e++")"
      show' e           = show e

instance Read Exp where
  readsPrec _ = readP_to_S expr

expr :: ReadP Exp
expr    = term   `chainl1` addop
term    = factor `chainl1` mulop
factor  = parens expr +++ nat

mulop   = do { skipSpaces
             ; string "*"
             ; skipSpaces
             ; return (:*)
             }
addop   = do { skipSpaces
             ; string "+"
             ; skipSpaces
             ; return (:+)
             }

nat :: ReadP Exp
nat = peano >>= return . ENat

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

data Exp' (e :: Exp) where
  ENat' :: Nat' n -> Exp' (ENat n)
  (:+:) :: Exp' e1 -> Exp' e2 -> Exp' (e1 :+ e2)
  (:*:) :: Exp' e1 -> Exp' e2 -> Exp' (e1 :* e2)

instance Show (Exp' e) where
  show (ENat' n)   = show n
  show (e1 :+: e2) = unwords [show e1,"+",show e2]
  show (e1 :*: e2) = unwords [show' e1,"*",show' e2]
    where
      show' e@(_ :+: _) = "("++show e++")"
      show' e           = show e

-- ----------------------------------------------------

ex010701 :: Exp
ex010701 = read "(S(Z) + (S(S(Z)) * Z)) + S(Z)"

ex010702 :: Exp
ex010702 = read "S(Z) + ((S(S(Z)) * Z) + S(Z))"

ex010703 :: Exp
ex010703 = read "(S(Z) * S(S(Z))) * (S(S(S(Z))) + S(S(Z)))"

ex010704 :: Exp
ex010704 = read "((S(Z) * S(S(Z))) * S(S(S(Z)))) + S(S(Z))"

ex010705 :: Exp
ex010705 = read "(S(Z) * S(S(Z))) + (Z * S(S(S(Z))))"

ex010706 :: Exp
ex010706 = read "(S(Z) * (S(S(Z)) +Z)) * S(S(S(Z)))"

ex010707 :: Exp
ex010707 = read "S(Z) * ((S(S(Z)) +Z) * S(S(S(Z))))"

