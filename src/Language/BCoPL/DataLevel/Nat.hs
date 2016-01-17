module Language.BCoPL.DataLevel.Nat (
      -- * Types
      Nat(..)
    , Judge(..)
      -- * Deduction
    , deduce
      -- * Session for deriving judge on 'Nat'
    , session
    , session'
    ) where

import Language.BCoPL.DataLevel.Peano (Nat(..))
import Language.BCoPL.DataLevel.Derivation (Tree(..),Deducer,sessionGen,sessionGen')

data Judge = Plus  { k,m,n :: Nat }
           | Times { k,m,n :: Nat }
           deriving (Eq)

instance Show Judge where
  show (Plus k m n)  = unwords [show k,"plus",show m,"is",show n]
  show (Times k m n) = unwords [show k,"times",show m,"is",show n]

instance Read Judge where
  readsPrec _ s = case words s of
    n1:"plus":n2:"is":n3:rs  -> [(Plus (read n1) (read n2) (read n3),"")]
    n1:"times":n2:"is":n3:rs -> [(Times (read n1) (read n2) (read n3),"")]
    _                        -> error ("Invalid syntax for 'Nat judgement': "++s)

deduce :: Deducer Judge
deduce j = case j of
  Plus Z n1 n2 | n1 == n2 -> [Node ("P-Zero",j) []]
  Plus (S n1) n2 (S n3)   -> [Node ("P-Succ",j) [j'] 
                             | j' <- deduce (Plus n1 n2 n3)
                             ]
  Times Z _ n  | n == Z   -> [Node ("T-Zero",j) []]
  Times (S n1) n2 n4      -> [Node ("T-Succ",j) [j1,j2] 
                             | n3 <- [Z .. n4]
                             , j2 <- deduce (Plus n2 n3 n4)
                             , j1 <- deduce (Times n1 n2 n3)
                             ]
  _                       -> []

session,session' :: IO ()
session = sessionGen ("Nat> ",deduce)
session' = sessionGen' ("Nat> ",deduce)

