module Language.BCoPL.EvalNatExp (
    -- * Types
    Nat(..)
  , Exp(..)
  , Judge
    -- * Deducer
  , deduce
    -- * Session for deriving judge on evaluating expression
  , session
  ) where

import Data.Char (toLower)

import Language.BCoPL.Exp (Exp(..))
import Language.BCoPL.Peano (Nat(..))
import qualified Language.BCoPL.Nat as Nat (Judge(..),deduce)
import Language.BCoPL.Derivation (Tree(..),Deducer,Derivation,sessionGen)

data Judge = OnNat Nat.Judge
           | EvalTo Exp Nat

instance Show Judge where
  show (OnNat jn)   = show jn
  show (EvalTo e n) = unwords [show e,"evalto",show n]

instance Read Judge where
  readsPrec _ s = case break (("evalto" ==) . map toLower) (words s) of
    (es,_:n:_) -> [(EvalTo (read (concat es)) (read n),"")]
    _          -> error ("Invalid syntax for 'EvalNatExp' judgement: "++s)

toJudge :: Derivation Nat.Judge -> Derivation Judge
toJudge (Node (s,nj) ts) = Node (s,OnNat nj) (map toJudge ts)

deduce :: Deducer Judge
deduce j = case j of
  OnNat nj    -> map toJudge (Nat.deduce nj)
  EvalTo e n  -> case e of
    Nat n' | n' == n -> [ Node ("E-Const",j) [] ]
    e1 :+: e2        -> [ Node ("E-Plus",j) [j1,j2,j3]
                        | n1 <- [Z .. n]
                        , j1 <- deduce (EvalTo e1 n1)
                        , n2 <- [Z .. n]
                        , j2 <- deduce (EvalTo e2 n2)
                        , j3 <- deduce (OnNat (Nat.Plus n1 n2 n))
                        ]
    e1 :*: e2        -> [ Node ("E-Times",j) [j1,j2,j3]
                        | n1 <- [Z .. n]
                        , j1 <- deduce (EvalTo e1 n1)
                        , n2 <- [Z .. n]
                        , j2 <- deduce (EvalTo e2 n2)
                        , j3 <- deduce (OnNat (Nat.Times n1 n2 n))
                        ]
    _                -> []

session :: IO ()
session = sessionGen ("EvalNat> ",deduce)
