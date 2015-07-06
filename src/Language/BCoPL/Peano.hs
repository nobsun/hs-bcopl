{-# LANGUAGE NPlusKPatterns #-}
module Language.BCoPL.Peano(
    -- * Type
    Nat (..)
  ) where

data Nat = Z 
         | S Nat
         deriving (Eq,Ord,Read)

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

