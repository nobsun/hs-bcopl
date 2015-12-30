{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
module Language.BCoPL.Nat where

import Language.BCoPL.Peano

data Plus (n1 :: Nat) (n2 :: Nat) (n3 :: Nat) where
  PZero :: Nat' n -> Plus Z n n
  PSucc :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus (S n1) n2 (S n3)

data Times (n1 :: Nat) (n2 :: Nat) (n4 :: Nat) where
  TZero :: Nat' n -> Times Z n Z
  TSucc :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4
        -> Times n1 n2 n3 -> Plus n2 n3 n4
        -> Times (S n1) n2 n4

instance Show (Plus n1 n2 n3) where
  show (PZero n) = unwords [show Z',"plus",show n,"is",show n,"by","P-Zero","{","}"]
  show (PSucc n1 n2 n3 k)
    = unwords [show (S' n1),"plus",show n2,"is",show (S' n3),"by","P-Succ"
              ,"{",show k,"}"]

instance Show (Times n1 n2 n3) where
  show (TZero n) = unwords [show Z',"times",show n,"is",show Z',"by","T-Zero","{","}"]
  show (TSucc n1 n2 _ n3 j k)
    = unwords [show (S' n1),"times",show n2,"is",show n3,"by","T-Succ","{"
              ,show j,";",show k
              ,"}"
              ]

instance Read (Plus Z Z Z) where
  readsPrec _ s = case words s of 
    "Z":"plus":"Z":"is":"Z":_ -> [(PZero Z',"")]
    pat                       -> case pat of {}
instance Read (Nat' n) => Read (Plus Z (S n) (S n)) where
  readsPrec _ s = case words s of
    "Z":"plus":ns:"is":_:_ -> [(PZero (S'(read ns)),"")]
    pat                    -> case pat of {}
instance (Read (Nat' n1),Read (Nat' n2),Read (Nat' n3),
          Read (Plus n1 n2 n3)) => Read (Plus (S n1) n2 (S n3)) where
  readsPrec _ s = case words s of
    ('S':'(':rs1):"plus":rs2:"is":('S':'(':rs3):_
      -> [(PSucc n1 n2 n3 (read (unwords [init rs1,"plus",rs2,"is",init rs3])),"")]
         where 
           n1 = read (init rs1)
           n2 = read rs2
           n3 = read (init rs3)
    pat -> case pat of {}

-- 練習問題 1.2 (1)

ex010201 :: Plus (S(S(S Z))) (S Z) (S(S(S(S Z))))
ex010201 = theoryP3 (theoryP2 (theoryP1 postulateP0))
  where
    theoryP3 :: Plus (S(S Z)) (S Z) (S(S(S Z))) -> Plus (S(S(S Z))) (S Z) (S(S(S(S Z))))
    theoryP3 =  PSucc (S'(S' Z')) (S' Z') (S'(S'(S' Z')))
    theoryP2 :: Plus (S Z) (S Z) (S(S Z)) -> Plus (S(S Z)) (S Z) (S(S(S Z)))
    theoryP2 =  PSucc (S' Z') (S' Z') (S'(S' Z'))
    theoryP1 :: Plus Z (S Z) (S Z) -> Plus (S Z) (S Z) (S(S Z))
    theoryP1 =  PSucc Z' (S' Z') (S' Z')
    postulateP0 :: Plus Z (S Z) (S Z)
    postulateP0 =  PZero (S' Z')

-- 練習問題 1.2 (2)

ex010202 :: Plus (S Z) (S(S(S Z))) (S(S(S(S Z))))
ex010202 =  theoryP1 postulateP0
  where
    theoryP1 :: Plus Z (S(S(S Z))) (S(S(S Z))) -> Plus (S Z) (S(S(S Z))) (S(S(S(S Z))))
    theoryP1 =  PSucc Z' (S'(S'(S' Z'))) (S'(S'(S' Z')))
    postulateP0 :: Plus Z (S(S(S Z))) (S(S(S Z)))
    postulateP0 =  PZero (S'(S'(S' Z')))

-- 練習問題 1.2 (3)

ex010203 :: Times (S(S(S Z))) Z Z
ex010203 =  theoryT3 (theoryT2 (theoryT1 postulateT0 postulateP0) postulateP0) postulateP0
  where
    theoryT3 :: Times (S(S Z)) Z Z -> Plus Z Z Z -> Times (S(S(S Z))) Z Z
    theoryT3 =  TSucc (S'(S' Z')) Z' Z' Z'
    theoryT2 :: Times (S Z) Z Z -> Plus Z Z Z -> Times (S(S Z)) Z Z
    theoryT2 =  TSucc (S' Z') Z' Z' Z'
    theoryT1 :: Times Z Z Z -> Plus Z Z Z -> Times (S Z) Z Z
    theoryT1 =  TSucc Z' Z' Z' Z'
    postulateT0 :: Times Z Z Z
    postulateT0 =  TZero Z'
    postulateP0 :: Plus Z Z Z
    postulateP0 =  PZero Z'

-- 練習問題 1.4 

ex010401 :: Plus (S(S(S Z))) (S Z) (S(S(S(S Z))))
ex010401 = theoryP3 (theoryP2 (theoryP1 postulateP0))
  where
    theoryP3 :: Plus (S(S Z)) (S Z) (S(S(S Z))) -> Plus (S(S(S Z))) (S Z) (S(S(S(S Z))))
    theoryP3 =  PSucc (S'(S' Z')) (S' Z') (S'(S'(S' Z')))
    theoryP2 :: Plus (S Z) (S Z) (S(S Z)) -> Plus (S(S Z)) (S Z) (S(S(S Z)))
    theoryP2 =  PSucc (S' Z') (S' Z') (S'(S' Z'))
    theoryP1 :: Plus Z (S Z) (S Z) -> Plus (S Z) (S Z) (S(S Z))
    theoryP1 =  PSucc Z' (S' Z') (S' Z')
    postulateP0 :: Plus Z (S Z) (S Z)
    postulateP0 =  PZero (S' Z')

ex010402 :: Plus (S Z) (S(S(S Z))) (S(S(S(S Z))))
ex010402 =  theoryP1 postulateP0
  where
    theoryP1 :: Plus Z (S(S(S Z))) (S(S(S Z))) -> Plus (S Z) (S(S(S Z))) (S(S(S(S Z))))
    theoryP1 =  PSucc Z' (S'(S'(S' Z'))) (S'(S'(S' Z')))
    postulateP0 :: Plus Z (S(S(S Z))) (S(S(S Z)))
    postulateP0 =  PZero (S'(S'(S' Z')))

ex010403 :: Times (S(S(S Z))) Z Z
ex010403 =  TSucc (S'(S' Z')) Z' Z' Z' 
                  (TSucc (S' Z') Z' Z' Z'
                         (TSucc Z' Z' Z' Z'
                                (TZero Z')
                                (PZero Z'))
                         (PZero Z'))
                  (PZero Z')
