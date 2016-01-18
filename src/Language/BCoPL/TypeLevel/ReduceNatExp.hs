{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
module Language.BCoPL.TypeLevel.ReduceNatExp where

import Language.BCoPL.TypeLevel.Peano
import Language.BCoPL.TypeLevel.Nat
import Language.BCoPL.TypeLevel.Exp

data (:--->) (e1 :: Exp) (e2 :: Exp) where
  RPlus :: Nat' n1 -> Nat' n2 -> Nat' n3
        -> Plus n1 n2 n3
        -> (ENat n1 :＋ ENat n2) :---> ENat n3
  RTimes :: Nat' n1 -> Nat' n2 -> Nat' n3
         -> Times n1 n2 n3
         -> (ENat n1 :× ENat n2) :---> ENat n3
  RPlusL :: Exp' e1 -> Exp' e1' -> Exp' e2
         -> e1 :---> e1' -> (e1 :＋ e2) :---> (e1' :＋ e2)
  RPlusR :: Exp' e1 -> Exp' e2 -> Exp' e2'
         -> e2 :---> e2' -> (e1 :＋ e2) :---> (e1 :＋ e2')
  RTimesL :: Exp' e1 -> Exp' e1' -> Exp' e2
          -> e1 :---> e1' -> (e1 :× e2) :---> (e1' :× e2)
  RTimesR :: Exp' e1 -> Exp' e2 -> Exp' e2'
          -> e2 :---> e2' -> (e1 :× e2) :---> (e1 :× e2')

data (:-*->) (e1 :: Exp) (e2 :: Exp) where
  MRZero  :: Exp' e
          -> e :-*-> e
  MROne   :: Exp' e -> Exp' e'
          -> e :---> e'
          -> e :-*-> e'
  MRMulti :: Exp' e -> Exp' e' -> Exp' e''
          -> e :-*-> e' -> e' :-*-> e''
          -> e :-*-> e''

normalize :: (e :-*-> e') -> (e :-*-> e')
normalize mr = case mr of
  MRZero _ -> mr
  MROne _ _ _ -> mr
  MRMulti e1 e2 e3 mr1 mr2 -> case mr2 of
    MRZero _    -> normalize mr1
    MROne _ _ _ -> MRMulti e1 e2 e3 (normalize mr1) mr2
    MRMulti _ e4 _ mr21 mr22 -> normalize (MRMulti e1 e4 e3 (normalize (MRMulti e1 e2 e4 (normalize mr1) (normalize mr21))) (normalize mr22))

                                                                

data (:-/->) (e1 :: Exp) (e2 :: Exp) where
  DRPlus :: Nat' n1 -> Nat' n2 -> Nat' n3
         -> Plus n1 n2 n3
         -> (ENat n1 :＋ ENat n2) :-/-> (ENat n3)
  DRTimes :: Nat' n1 -> Nat' n2 -> Nat' n3
          -> Times n1 n2 n3
          -> (ENat n1 :× ENat n2) :-/-> (ENat n3)
  DRPlusL :: Exp' e1 -> Exp' e1' -> Exp' e2
          -> e1 :-/-> e1' 
          -> (e1 :＋ e2) :-/-> (e1' :＋ e2)
  DRPlusR :: Nat' n1 -> Exp' e2 -> Exp' e2'
          -> e2 :-/-> e2'
          -> (ENat n1 :＋ e2) :-/-> (ENat n1 :＋ e2')
  DRTimesL :: Exp' e1 -> Exp' e1' -> Exp' e2
           -> e1 :-/-> e1' 
           -> (e1 :× e2) :-/-> (e1' :× e2)
  DRTimesR :: Nat' n1 -> Exp' e2 -> Exp' e2'
           -> e2 :-/-> e2'
           -> (ENat n1 :× e2) :-/-> (ENat n1 :× e2')

data (:-\->) (e1 :: Exp) (e2 :: Exp) where
  DRPlus' :: Nat' n1 -> Nat' n2 -> Nat' n3
          -> Plus n1 n2 n3
          -> (ENat n1 :＋ ENat n2) :-\-> (ENat n3)
  DRTimes' :: Nat' n1 -> Nat' n2 -> Nat' n3
           -> Times n1 n2 n3
           -> (ENat n1 :× ENat n2) :-\-> (ENat n3)
  DRPlusL' :: Exp' e1 -> Exp' e1' -> Nat' n2
           -> e1 :-\-> e1' 
           -> (e1 :＋ ENat n2) :-\-> (e1' :＋ ENat n2)
  DRPlusR' :: Exp' e1 -> Exp' e2 -> Exp' e2'
           -> e2 :-\-> e2'
           -> (e1 :＋ e2) :-\-> (e1 :＋ e2')
  DRTimesL' :: Exp' e1 -> Exp' e1' -> Nat' n2
            -> e1 :-\-> e1' 
            -> (e1 :× ENat n2) :-\-> (e1' :× ENat n2)
  DRTimesR' :: Exp' e1 -> Exp' e2 -> Exp' e2'
            -> e2 :-\-> e2'
            -> (e1 :× e2) :-\-> (e1 :× e2')


-- ------------------------------------------

ex010901 :: (ENat Z :＋ ENat (S(S(Z)))) :-*-> ENat (S(S(Z)))
ex010901 =  MROne (ENat' Z' :＋: ENat' (S'(S' Z'))) (ENat' (S'(S' Z')))
                  (RPlus Z' (S'(S' Z')) (S'(S' Z'))
                         (PZero (S'(S' Z'))))

ex010902 :: ((ENat (S Z) :× ENat (S Z)) :＋ (ENat (S Z) :× ENat (S Z)))
      :-/-> (ENat (S Z) :＋ (ENat (S Z) :× ENat (S Z)))
ex010902 =  DRPlusL (ENat' (S' Z') :×: ENat' (S' Z')) (ENat' (S' Z')) (ENat' (S' Z') :×: ENat' (S' Z'))
                    (DRTimes (S' Z') (S' Z') (S' Z')
                             (TSucc Z' (S' Z') Z' (S' Z')
                                    (TZero (S' Z'))
                                    (PSucc Z' Z'  Z' 
                                           (PZero Z'))))

ex010903 :: ((ENat (S Z) :× ENat (S Z)) :＋ (ENat (S Z) :× ENat (S Z)))
      :---> ((ENat (S Z) :× ENat (S Z)) :＋ ENat (S Z))
ex010903 =  RPlusR (ENat' (S' Z') :×: ENat' (S' Z')) (ENat' (S' Z') :×: ENat' (S' Z')) (ENat' (S' Z'))
                   (RTimes (S' Z') (S' Z') (S' Z')
                           (TSucc Z' (S' Z') Z' (S' Z')
                                  (TZero (S' Z'))
                                  (PSucc Z' Z' Z'
                                         (PZero Z'))))

ex010904 :: ((ENat (S Z) :× ENat (S Z)) :＋ (ENat (S Z) :× ENat (S Z)))
      :-*-> (ENat (S(S Z)))
ex010904 =  MRMulti ((ENat' (S' Z') :×: ENat' (S' Z')) :＋: (ENat' (S' Z') :×: ENat' (S' Z')))
                    (ENat' (S' Z') :＋: ENat' (S' Z'))
                    (ENat' (S'(S' Z')))
                    (MRMulti ((ENat' (S' Z') :×: ENat' (S' Z')) :＋: (ENat' (S' Z') :×: ENat' (S' Z')))
                             (ENat' (S' Z') :＋: (ENat' (S' Z') :×: ENat' (S' Z')))
                             (ENat' (S' Z') :＋: ENat' (S' Z'))
                             (MROne ((ENat' (S' Z') :×: ENat' (S' Z')) :＋: (ENat' (S' Z') :×: ENat' (S' Z')))
                                    (ENat' (S' Z') :＋: (ENat' (S' Z') :×: ENat' (S' Z')))
                                    (RPlusL (ENat' (S' Z') :×: ENat' (S' Z')) (ENat' (S' Z')) (ENat' (S' Z') :×: ENat' (S' Z'))
                                            (RTimes (S' Z') (S' Z') (S' Z')
                                                    (TSucc Z' (S' Z') Z' (S' Z')
                                                           (TZero (S' Z'))
                                                           (PSucc Z' Z' Z'
                                                                  (PZero Z'))))))
                             (MROne (ENat' (S' Z') :＋: (ENat' (S' Z') :×: ENat' (S' Z')))
                                    (ENat' (S' Z') :＋: ENat' (S' Z'))
                                    (RPlusR (ENat' (S' Z')) (ENat' (S' Z') :×: ENat' (S' Z')) (ENat' (S' Z'))
                                            (RTimes (S' Z') (S' Z') (S' Z')
                                                    (TSucc Z' (S' Z') Z' (S' Z')
                                                           (TZero (S' Z'))
                                                           (PSucc Z' Z' Z'
                                                                  (PZero Z')))))))
                    (MROne (ENat' (S' Z') :＋: ENat' (S' Z')) (ENat' (S'(S' Z')))
                           (RPlus (S' Z') (S' Z') (S'(S' Z'))
                                  (PSucc Z' (S' Z') (S' Z')
                                         (PZero (S' Z')))))


ex011001 :: ((ENat (S Z) :× ENat (S Z)) :＋ (ENat (S Z) :× ENat (S Z)))
      :-\-> ((ENat (S Z) :× ENat (S Z)) :＋ ENat (S Z))
ex011001 =  DRPlusR' (ENat' (S' Z') :×: ENat' (S' Z')) (ENat' (S' Z') :×: ENat' (S' Z')) (ENat' (S' Z'))
                     (DRTimes' (S' Z') (S' Z') (S' Z')
                               (TSucc Z' (S' Z') Z' (S' Z')
                                      (TZero (S' Z'))
                                      (PSucc Z' Z' Z'
                                             (PZero Z'))))

ex011002 :: ((ENat (S Z) :× ENat (S Z)) :＋ ENat (S Z))
      :-\-> (ENat (S Z) :＋ ENat (S Z))
ex011002 =  DRPlusL' (ENat' (S' Z') :×: ENat' (S' Z')) (ENat' (S' Z')) (S' Z')
                     (DRTimes' (S' Z') (S' Z') (S' Z')
                               (TSucc Z' (S' Z') Z' (S' Z')
                                      (TZero (S' Z'))
                                      (PSucc Z' Z' Z'
                                             (PZero Z'))))
