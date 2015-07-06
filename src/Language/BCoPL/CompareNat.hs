module Language.BCoPL.CompareNat (
    -- * Types
    Nat (..)
  , Judge (..)
    -- * Deducer
  , deduce1
  , deduce2
  , deduce3
    -- * Session for deriving judgement on comparing 'Nat'
  , session1
  , session2
  , session3
  , session1'
  , session2'
  , session3'
  ) where

import Language.BCoPL.Peano (Nat(..))
import Language.BCoPL.Derivation (Tree(..),Deducer,sessionGen,sessionGen')

data Judge = LessThan Nat Nat
           deriving (Eq)

instance Show Judge where
  show (LessThan m n) = unwords [show m,"is less than",show n]

instance Read Judge where
  readsPrec _ s = case words s of
    n1:"is":"less":"than":n2:_ -> [(LessThan (read n1) (read n2),"")]
    _                          -> error ("Invalid syntax for 'CompareNat judgement': "++s)

deduce1 :: Deducer Judge
deduce1 j = case j of
  LessThan n (S n')
    | n == n'    -> [ Node ("L-Succ",j) [] ]
  LessThan n1 n3 -> [ Node ("L-Trans",j) [j1,j2 ]
                    | n2 <- [S n1 .. n3]
                    , j1 <- deduce1 (LessThan n1 n2)
                    , j2 <- deduce1 (LessThan n2 n3)
                    ]

deduce2 :: Deducer Judge
deduce2 j = case j of
  LessThan Z      (S _)  -> [ Node ("L-Zero",j) [] ]
  LessThan (S n1) (S n2) -> [ Node ("L-SuccSucc",j) [j']
                            | j' <- deduce2 (LessThan n1 n2)
                            ]
  _                      -> []

deduce3 :: Deducer Judge
deduce3 j = case j of
  LessThan n (S n')
    | n == n'        -> [ Node ("L-Succ",j) [] ]
  LessThan n1 (S n2) -> [ Node ("L-SuccR",j) [j']
                        | j' <- deduce3 (LessThan n1 n2)
                        ]
  _                  -> []

session1,session2,session3 :: IO ()
session1 = sessionGen ("CompareNat1> ",deduce1)
session2 = sessionGen ("CompareNat2> ",deduce2)
session3 = sessionGen ("CompareNat3> ",deduce3)

session1',session2',session3' :: IO ()
session1' = sessionGen' ("CompareNat1> ",deduce1)
session2' = sessionGen' ("CompareNat2> ",deduce2)
session3' = sessionGen' ("CompareNat3> ",deduce3)
