{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
module Language.BCoPL.CompareNat where

import Language.BCoPL.Peano

data LessThan1 (n1 :: Nat) (n2 :: Nat) where
  LSucc1  :: Nat' n -> LessThan1 n (S n)
  LTrans1 :: Nat' n1 -> Nat' n2 -> Nat' n3
          -> LessThan1 n1 n2 -> LessThan1 n2 n3
          -> LessThan1 n1 n3

instance Show (LessThan1 n1 n2) where
  show (LSucc1 n)
    = unwords [show n,"is","less","than",show (S' n),"by","L-Succ","{","}"]
  show (LTrans1 n1 _ n3 j1 j2)
    = unwords [show n1,"is","less","than",show n3,"by","L-Trans","{"
              ,show j1,";",show j2
              ,"}"
              ]

data LessThan2 (n1 :: Nat) (n2 :: Nat) where
  LZero2 :: Nat' n -> LessThan2 Z (S n)
  LSuccSucc2 :: Nat' n1 -> Nat' n2 -> LessThan2 n1 n2 -> LessThan2 (S n1) (S n2)

instance Show (LessThan2 n1 n2) where
  show (LZero2 n)
    = unwords [show Z',"is","less","than",show (S' n),"by","L-Zero","{","}"]
  show (LSuccSucc2 n1 n2 j)
    = unwords [show (S' n1),"is","less","than",show (S' n2),"by","L-SuccSucc","{"
              ,show j
              ,"}"
              ]

data LessThan3 (n1 :: Nat) (n2 :: Nat) where
  LSucc3 ::  Nat' n -> LessThan3 n (S n)
  LSuccR3 :: Nat' n1 -> Nat' n2 -> LessThan3 n1 n2 -> LessThan3 n1 (S n2)

instance Show (LessThan3 n1 n2) where
  show (LSucc3 n) 
    = unwords [show n,"is","less","than",show (S' n),"by","L-Succ","{","}"]
  show (LSuccR3 n1 n2 j)
    = unwords [show n1,"is","less","than",show (S' n2),"by","L-SuccR","{"
              ,show j
              ,"}"
              ]

-- 練習問題 1.5

ex010501_1 :: LessThan1 Z (S(S Z))
ex010501_1 =  LTrans1 Z' (S' Z') (S'(S' Z')) 
                      (LSucc1 Z') (LSucc1 (S' Z'))

ex010501_2 :: LessThan2 Z (S(S Z))
ex010501_2 =  LZero2 (S' Z')

ex010501_3 :: LessThan3 Z (S(S Z))
ex010501_3 =  LSuccR3 Z' (S' Z') (LSucc3 Z')

ex010502_1 :: LessThan1 (S(S Z)) (S(S(S(S Z))))
ex010502_1 =  LTrans1 (S'(S' Z')) (S'(S'(S' Z'))) (S'(S'(S'(S' Z'))))
                      (LSucc1 (S'(S' Z'))) (LSucc1 (S'(S'(S' Z'))))

ex010502_2 :: LessThan2 (S(S Z)) (S(S(S(S Z))))
ex010502_2 =  LSuccSucc2 (S' Z') (S'(S'(S' Z')))
                         (LSuccSucc2 Z' (S'(S' Z')) (LZero2 (S' Z')))

ex010502_3 :: LessThan3 (S(S Z)) (S(S(S(S Z))))
ex010502_3 =  LSuccR3 (S'(S' Z')) (S'(S'(S' Z'))) (LSucc3 (S'(S' Z')))
