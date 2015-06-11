module Language.BCoPL.CompareNat (
    -- * Types
    Nat (..)
  , Judge (..)
    -- * Deduction
  , deduce1
  , deduce2
  , deduce3
  , derivation
  ) where

import Debug.Trace(trace)

import Language.BCoPL.Nat (Nat(..))
import Language.BCoPL.Derivation (Tree(..),Derivation,Deducer,derivation)

data Judge = LessThan Nat Nat deriving (Eq)

instance Show Judge where
  show (LessThan m n) = show m ++ " is less than " ++ show n

deduce1 :: Deducer Judge
deduce1 j = case j of
  LessThan n (S n')
    | n == n'    -> [Node ("L-Succ",j) []]
  LessThan n1 n3 -> [S n1 .. n3] >>= \ n2 ->                -- 反則？
                    deduce1 (LessThan n1 n2) >>= \ j1 ->
                    deduce1 (LessThan n2 n3) >>= \ j2 ->
                    [Node ("L-Trans",j) [j1,j2]]
  _              -> []

deduce2 :: Deducer Judge
deduce2 j = case j of
  LessThan Z      (S _)  -> [Node ("L-Zero",j) []]
  LessThan (S n1) (S n2) -> deduce2 (LessThan n1 n2) >>= \ j' ->
                            [Node ("L-SuccSucc",j) [j']]
  _                      -> []

deduce3 :: Deducer Judge
deduce3 j = case j of
  LessThan n (S n')
    | n == n'        -> [Node ("L-Succ",j) []]
  LessThan n1 (S n2) -> deduce3 (LessThan n1 n2) >>= \ j' ->
                        [Node ("L-SuccR",j) [j']]
