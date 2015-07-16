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
module Language.BCoPL.ReduceNatExp where

import Language.BCoPL.Peano
import Language.BCoPL.Nat
import Language.BCoPL.Exp

data (:--->) (e1 :: Exp) (e2 :: Exp) where
  RPlus :: Nat' n1 -> Nat' n2 -> Nat' n3
        -> Plus n1 n2 n3
        -> (ENat n1 :+ ENat n2) :---> ENat n3
  RTimes :: Nat' n1 -> Nat' n2 -> Nat' n3
         -> Times n1 n2 n3
         -> (ENat n1 :* ENat n2) :---> ENat n3
  RPlusL :: Exp' e1 -> Exp' e1' -> Exp' e2
         -> e1 :---> e1' -> (e1 :+ e2) :---> (e1' :+ e2)
  RPlusR :: Exp' e1 -> Exp' e2 -> Exp' e2'
         -> e2 :---> e2' -> (e1 :+ e2) :---> (e1 :+ e2')
  RTimesL :: Exp' e1 -> Exp' e1' -> Exp' e2
          -> e1 :---> e1' -> (e1 :* e2) :---> (e1' :* e2)
  RTimesR :: Exp' e1 -> Exp' e2 -> Exp' e2'
          -> e2 :---> e2' -> (e1 :* e2) :---> (e1 :* e2')

data (:-*->) (e1 :: Exp) (e2 :: Exp) where
  MRZero  :: Exp' e
          -> e :-*-> e
  MROne   :: Exp' e -> Exp' e'
          -> e :---> e'
          -> e :-*-> e'
  MRMulti :: Exp' e -> Exp' e' -> Exp' e''
          -> e :-*-> e' -> e' :-*-> e''
          -> e :-*-> e''

data (:-/->) (e1 :: Exp) (e2 :: Exp) where
  DRPlus :: Nat' n1 -> Nat' n2 -> Nat' n3
         -> Plus n1 n2 n3
         -> (ENat n1 :+ ENat n2) :-/-> (ENat n3)
  DRTimes :: Nat' n1 -> Nat' n2 -> Nat' n3
          -> Times n1 n2 n3
          -> (ENat n1 :* ENat n2) :-/-> (ENat n3)
  DRPlusL :: Exp' e1 -> Exp' e1' -> Exp' e2
          -> e1 :-/-> e1' 
          -> (e1 :+ e2) :-/-> (e1' :+ e2)
  DRPlusR :: Nat' n1 -> Exp' e2 -> Exp' e2'
          -> e2 :-/-> e2'
          -> (ENat n1 :+ e2) :-/-> (ENat n1 :+ e2')
  DRTimesL :: Exp' e1 -> Exp' e1' -> Exp' e2
           -> e1 :-/-> e1' 
           -> (e1 :* e2) :-/-> (e1' :* e2)
  DRTimesR :: Nat' n1 -> Exp' e2 -> Exp' e2'
           -> e2 :-/-> e2'
           -> (ENat n1 :* e2) :-/-> (ENat n1 :* e2')

data (:-\->) (e1 :: Exp) (e2 :: Exp) where
  DRPlus' :: Nat' n1 -> Nat' n2 -> Nat' n3
          -> Plus n1 n2 n3
          -> (ENat n1 :+ ENat n2) :-\-> (ENat n3)
  DRTimes' :: Nat' n1 -> Nat' n2 -> Nat' n3
           -> Times n1 n2 n3
           -> (ENat n1 :* ENat n2) :-\-> (ENat n3)
  DRPlusL' :: Exp' e1 -> Exp' e1' -> Nat' n2
           -> e1 :-\-> e1' 
           -> (e1 :+ ENat n2) :-\-> (e1' :+ ENat n2)
  DRPlusR' :: Exp' e1 -> Exp' e2 -> Exp' e2'
           -> e2 :-\-> e2'
           -> (e1 :+ e2) :-\-> (e1 :+ e2')
  DRTimesL' :: Exp' e1 -> Exp' e1' -> Nat' n2
            -> e1 :-\-> e1' 
            -> (e1 :* ENat n2) :-\-> (e1' :* ENat n2)
  DRTimesR' :: Exp' e1 -> Exp' e2 -> Exp' e2'
            -> e2 :-\-> e2'
            -> (e1 :* e2) :-\-> (e1 :* e2')

-- ------------------------------------------

ex010901 :: (ENat Z :+ ENat (S(S(Z)))) :-*-> ENat (S(S(Z)))
ex010901 =  MROne (ENat' Z' :+: ENat' (S'(S' Z'))) (ENat' (S'(S' Z')))
                  (RPlus Z' (S'(S' Z')) (S'(S' Z'))
                         (PZero (S'(S' Z'))))

ex010902 :: ((ENat (S Z) :* ENat (S Z)) :+ (ENat (S Z) :* ENat (S Z)))
      :-/-> (ENat (S Z) :+ (ENat (S Z) :* ENat (S Z)))
ex010902 =  DRPlusL (ENat' (S' Z') :*: ENat' (S' Z')) (ENat' (S' Z')) (ENat' (S' Z') :*: ENat' (S' Z'))
                    (DRTimes (S' Z') (S' Z') (S' Z')
                             (TSucc Z' (S' Z') Z' (S' Z')
                                    (TZero (S' Z'))
                                    (PSucc Z' Z'  Z' 
                                           (PZero Z'))))

ex010903 :: ((ENat (S Z) :* ENat (S Z)) :+ (ENat (S Z) :* ENat (S Z)))
      :---> ((ENat (S Z) :* ENat (S Z)) :+ ENat (S Z))
ex010903 =  RPlusR (ENat' (S' Z') :*: ENat' (S' Z')) (ENat' (S' Z') :*: ENat' (S' Z')) (ENat' (S' Z'))
                   (RTimes (S' Z') (S' Z') (S' Z')
                           (TSucc Z' (S' Z') Z' (S' Z')
                                  (TZero (S' Z'))
                                  (PSucc Z' Z' Z'
                                         (PZero Z'))))

ex010904 :: ((ENat (S Z) :* ENat (S Z)) :+ (ENat (S Z) :* ENat (S Z)))
      :-*-> (ENat (S(S Z)))
ex010904 =  MRMulti ((ENat' (S' Z') :*: ENat' (S' Z')) :+: (ENat' (S' Z') :*: ENat' (S' Z')))
                    (ENat' (S' Z') :+: ENat' (S' Z'))
                    (ENat' (S'(S' Z')))
                    (MRMulti ((ENat' (S' Z') :*: ENat' (S' Z')) :+: (ENat' (S' Z') :*: ENat' (S' Z')))
                             (ENat' (S' Z') :+: (ENat' (S' Z') :*: ENat' (S' Z')))
                             (ENat' (S' Z') :+: ENat' (S' Z'))
                             (MROne ((ENat' (S' Z') :*: ENat' (S' Z')) :+: (ENat' (S' Z') :*: ENat' (S' Z')))
                                    (ENat' (S' Z') :+: (ENat' (S' Z') :*: ENat' (S' Z')))
                                    (RPlusL (ENat' (S' Z') :*: ENat' (S' Z')) (ENat' (S' Z')) (ENat' (S' Z') :*: ENat' (S' Z'))
                                            (RTimes (S' Z') (S' Z') (S' Z')
                                                    (TSucc Z' (S' Z') Z' (S' Z')
                                                           (TZero (S' Z'))
                                                           (PSucc Z' Z' Z'
                                                                  (PZero Z'))))))
                             (MROne (ENat' (S' Z') :+: (ENat' (S' Z') :*: ENat' (S' Z')))
                                    (ENat' (S' Z') :+: ENat' (S' Z'))
                                    (RPlusR (ENat' (S' Z')) (ENat' (S' Z') :*: ENat' (S' Z')) (ENat' (S' Z'))
                                            (RTimes (S' Z') (S' Z') (S' Z')
                                                    (TSucc Z' (S' Z') Z' (S' Z')
                                                           (TZero (S' Z'))
                                                           (PSucc Z' Z' Z'
                                                                  (PZero Z')))))))
                    (MROne (ENat' (S' Z') :+: ENat' (S' Z')) (ENat' (S'(S' Z')))
                           (RPlus (S' Z') (S' Z') (S'(S' Z'))
                                  (PSucc Z' (S' Z') (S' Z')
                                         (PZero (S' Z')))))


ex011001 :: ((ENat (S Z) :* ENat (S Z)) :+ (ENat (S Z) :* ENat (S Z)))
      :-\-> ((ENat (S Z) :* ENat (S Z)) :+ ENat (S Z))
ex011001 =  DRPlusR' (ENat' (S' Z') :*: ENat' (S' Z')) (ENat' (S' Z') :*: ENat' (S' Z')) (ENat' (S' Z'))
                     (DRTimes' (S' Z') (S' Z') (S' Z')
                               (TSucc Z' (S' Z') Z' (S' Z')
                                      (TZero (S' Z'))
                                      (PSucc Z' Z' Z'
                                             (PZero Z'))))

ex011002 :: ((ENat (S Z) :* ENat (S Z)) :+ ENat (S Z))
      :-\-> (ENat (S Z) :+ ENat (S Z))
ex011002 =  DRPlusL' (ENat' (S' Z') :*: ENat' (S' Z')) (ENat' (S' Z')) (S' Z')
                     (DRTimes' (S' Z') (S' Z') (S' Z')
                               (TSucc Z' (S' Z') Z' (S' Z')
                                      (TZero (S' Z'))
                                      (PSucc Z' Z' Z'
                                             (PZero Z'))))
