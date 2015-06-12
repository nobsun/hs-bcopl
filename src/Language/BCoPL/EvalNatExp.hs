module Language.BCoPL.EvalNatExp (
    -- * Types
    Exp
  ) where

import Language.BCoPL.Nat (Nat(..))
import qualified Language.BCoPL.Nat as Nat (Judge(..),deduce)
import Language.BCoPL.Derivation (Tree(..),Derivation,Deducer,derivation)

data Exp = Nat Nat
         | Exp :+: Exp
         | Exp :*: Exp

instance Show Exp where
  show e = case e of
    Nat n     -> show n
    e1 :+: e2 -> show e1 ++ " + " ++ show e2
    e1 :*: e2 -> show' e1 ++ " * " ++ show' e2
    where
      show' e' = case e' of
        e1' :+: e2' -> "("++show e'++")"
        _           -> show e'

data Judge = OnNat Nat.Judge
           | EvalTo Exp Nat

instance Show Judge where
  show (OnNat jn)   = show jn
  show (EvalTo e n) = show e ++ " ￬ " ++ show n

toJudge :: Derivation Nat.Judge -> Derivation Judge
toJudge (Node (s,nj) ts) = Node (s,OnNat nj) (map toJudge ts)

deduce :: Deducer Judge
deduce j = case j of
  OnNat nj    -> map toJudge (Nat.deduce nj)
  EvalTo e n  -> case e of
    Nat n' | n' == n -> [Node ("E-Const",j) []]
    e1 :+: e2        -> [Z .. n]                           >>= \ n1 ->
                        deduce (EvalTo e1 n1)              >>= \ j1 ->
                        [Z .. n]                           >>= \ n2 ->
                        deduce (EvalTo e2 n2)              >>= \ j2 ->
                        deduce (OnNat (Nat.Plus n1 n2 n))  >>= \ j3 ->
                        [Node ("E-Plus",j) [j1,j2,j3]]
    e1 :*: e2        -> [Z .. n]                           >>= \ n1 ->
                        deduce (EvalTo e1 n1)              >>= \ j1 ->
                        [Z .. n]                           >>= \ n2 ->
                        deduce (EvalTo e2 n2)              >>= \ j2 ->
                        deduce (OnNat (Nat.Times n1 n2 n)) >>= \ j3 ->
                        [Node ("E-Times",j) [j1,j2,j3]]
    _                -> []
