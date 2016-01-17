module Language.BCoPL.DataLevel.EvalNatExp (
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

import Language.BCoPL.DataLevel.Exp (Exp(..))
import Language.BCoPL.DataLevel.Peano (Nat(..))
import qualified Language.BCoPL.DataLevel.Nat as Nat (Judge(..),deduce)
import Language.BCoPL.DataLevel.Derivation (Tree(..),Deducer,Derivation,sessionGen,sessionGen')

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
                        , j3 <- deduce (OnNat (Nat.Plus n1 n2 n))
                        , j2 <- deduce (EvalTo e2 n2)
                        ]
    e1 :*: e2        -> case n of
      Z                -> [ Node ("E-Times",j) [j1,j2,j3]
                          | j1 <- deduce (EvalTo e1 Z)
                          , n2 <- [Z ..]
                          , j2 <- deduce (EvalTo e2 n2)
                          , j3 <- deduce (OnNat (Nat.Times Z n2 Z))
                          ]
                          ++
                          [ Node ("E-Times",j) [j1,j2,j3]
                          | j2 <- deduce (EvalTo e2 Z)
                          , n1 <- [Z ..]
                          , j1 <- deduce (EvalTo e1 n1)
                          , j3 <- deduce (OnNat (Nat.Times n1 Z Z))
                          ]             
      _                -> [ Node ("E-Times",j) [j1,j2,j3]
                          | n1 <- [S Z .. ]
                          , j1 <- deduce (EvalTo e1 n1)
                          , n2 <- [S Z .. ]
                          , j2 <- deduce (EvalTo e2 n2)
                          , j3 <- deduce (OnNat (Nat.Times n1 n2 n))
                          ]
    _                -> []

session,session' :: IO ()
session  = sessionGen  ("EvalNat> ",deduce)
session' = sessionGen' ("EvalNat> ",deduce)
