{-# LANGUAGE NPlusKPatterns #-}
module Language.BCoPL.Nat (
    -- * Types
      Nat(..)
    , Judge(..)
    -- * Deduction
    , deduce
    -- * Derivation
    , derivation
    ) where

import Language.BCoPL.Derivation (Tree(..),Derivation,Deducer,derivation)

data Nat = Z 
         | S Nat
         deriving (Eq,Ord)

instance Show Nat where
  show Z     = "Z"
  show (S n) = "S("++show n++")"

instance Enum Nat where
  succ = S
  pred (S n) = n
  toEnum 0     = Z
  toEnum (n+1) = S (toEnum n)
  fromEnum Z     = 0
  fromEnum (S n) = succ (fromEnum n)

data Judge = Plus { k,m,n :: Nat }
           | Times { k,m,n :: Nat }
           deriving (Eq)

instance Show Judge where
  show (Plus k m n)  = show k ++ " plus " ++ show m ++ " is " ++ show n
  show (Times k m n) = show k ++ " times " ++ show m ++ " is " ++ show n

deduce :: Deducer Judge
deduce j = case j of
  Plus Z n1 n2 | n1 == n2 -> [Node ("P-Zero",j) []]
  Plus (S n1) n2 (S n3)   -> deduce (Plus n1 n2 n3) >>= \ j' ->
                             [Node ("P-Succ",j) [j']]
  Times Z _ n  | n == Z   -> return (Node ("T-Zero",j) [])
  Times (S n1) n2 n4      -> [Z .. n4] >>= \ n3 ->
                             deduce (Plus n2 n3 n4)  >>= \ j2 ->
                             deduce (Times n1 n2 n3) >>= \ j1 ->
                             [Node ("T-Succ",j) [j1,j2]]
  _                       -> []
