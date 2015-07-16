{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NPlusKPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
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

{- PlusとTimesをShowのインスタンスにできると便利なのだが -}
{-
instance Show (Nat' n) => Show (Plus Z n n) where
  show (PZero n) = unwords [show Z',"plus",show n,"is",show n,"by","P-Zero","{","}"]

instance (Show (Nat' n1), Show (Nat' n2), Show (Nat' n3), Show (Plus n1 n2 n3))
  => Show (Plus (S n1) n2 (S n3)) where
  show (PSucc n1 n2 n3 j1)
    = unwords [show (S' n1),"plus",show n2,"is",show (S' n3),"by","P-Succ"
              ,"{",show j1,"}"]

instance (Show (Nat' n))
  => Show (Times Z n Z) where
  show (TZero n) = unwords [show Z',"times", show n,"is",show Z',"by","{","}"]

instance (Show (Nat' n1),Show (Nat' n2),Show  (Nat' (n3 :: Nat)) ,Show (Nat' n4)
         ,Show (Times n1 n2 n3), Show (Plus n2 n3 n4))
       => Show (Times (S n1) n2 n4) where
  show (TSucc n1 n2 n3 n4 j1 j2)
    = unwords [show (S' n1),"times",show n2,"is",show n4,"by","T-Succ","{"
              ,show j1,";",show j2
              ,"}"
              ]
-}
-- instance Show (Plus n1 n2 n3) where
--   show _ = error "Show (Plus n1 n2 n3): Invalid Overlapping"

-- instance Show (Times n1 n2 n3) where
--   show _ = error "Show (Times n1 n2 n3): Invalid Overlapping"


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


