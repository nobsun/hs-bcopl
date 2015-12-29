{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Language.BCoPL.MetaTheory.Nat where

import Control.Applicative ((<*>))

import Language.BCoPL.Peano
import Language.BCoPL.CompareNat
import Language.BCoPL.Nat

import Language.BCoPL.Equiv
import Language.BCoPL.Exists

-- ---------------------------------------------
-- 
-- type family (m :: Nat) :+ (n :: Nat) :: Nat
-- type instance Z :+ n = n
-- type instance (S m) :+ n = S (m :+ n)
-- type family (m :: Nat) :* (n :: Nat) :: Nat
-- type instance     Z :* n = Z
-- type instance (S m) :* n = (m :* n) :+ n
-- let {add :: Nat' n1 -> Nat' n2 -> Nat' (n1 :+ n2); add Z' n2 = n2; add (S' n1) n2 = S' (add n1 n2) }

type family (m :: Nat) :+ (n :: Nat) :: Nat
type instance Z :+ n = n
type instance (S m) :+ n = S (m :+ n)
type family (m :: Nat) :* (n :: Nat) :: Nat
type instance     Z :* n = Z
type instance (S m) :* n = (m :* n) :+ n

add :: Nat' n1 -> Nat' n2 -> Nat' (n1 :+ n2)
add Z' n2 = n2
add (S' n1) n2 = S' (add n1 n2)

-- 定理 2.1 加法単位元

-- | 左単位元
--
-- >>> zeroPlus Z'
-- Z plus Z is Z by P-Zero { }
-- >>> zeroPlus (S'(S'(S' Z')))
-- Z plus S(S(S(Z))) is S(S(S(Z))) by P-Zero { }
zeroPlus  :: Nat' n -> Plus Z n n
zeroPlus = PZero

-- | 右単位元
--
-- >>> plusZero Z'
-- Z plus Z is Z by P-Zero { }
-- >>> plusZero (S'(S'(S' Z')))
-- S(S(S(Z))) plus Z is S(S(S(Z))) by P-Succ { S(S(Z)) plus Z is S(S(Z)) by P-Succ { S(Z) plus Z is S(Z) by P-Succ { Z plus Z is Z by P-Zero { } } } }
plusZero :: Nat' n -> Plus n Z n
plusZero Z'     = PZero Z'
plusZero (S' n) = PSucc n Z' n (plusZero n)

unitZeroPlus  :: Nat' n -> (Plus Z n n, Plus n Z n)
unitZeroPlus n = (zeroPlus n, plusZero n)

eqZeroPlus :: Nat' n -> Nat' n' -> Plus Z n n' -> n :=: n'
eqZeroPlus _ _ (PZero _) = Refl

eqPlusZero :: Nat' n -> Nat' n' -> Plus n Z n' -> n :=: n'
eqPlusZero Z' n' (PZero _)  = eqZeroPlus Z' n' (PZero n')
eqPlusZero (S' n) _ (PSucc _ _ n' j) = eqCong (eqPlusZero n n' j)

-- 定理 2.2 加法唯一性

-- | 加法唯一性
--
-- >>> plusUnique Z' (S'(S' Z')) (S'(S' Z')) (add (S' Z') (S' Z')) (PZero (S'(S' Z'))) (PZero (add (S' Z') (S' Z')))
-- >>> Refl

plusUnique :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4
           -> Plus n1 n2 n3 -> Plus n1 n2 n4
           -> n3 :=: n4
plusUnique Z' n2 n3 n4 j@(PZero _) k@(PZero _) 
  = eqTrans (eqSym (eqZeroPlus n2 n3 j)) (eqZeroPlus n2 n4 k)
plusUnique (S' n1) n2 (S' n3) (S' n4) (PSucc _ _ _ j) (PSucc _ _ _ j')
  = eqCong (plusUnique n1 n2 n3 n4 j j')

-- 定理 2.3 加法閉包性

-- | 加法閉包性
--
-- >>> plusClosure Z' (S' Z)
--
plusClosure :: Nat' n1 -> Nat' n2 -> Exists Nat' (Plus n1 n2)
plusClosure Z' n2       = ExIntro n2 (PZero n2)
plusClosure (S' n1) n2 = case plusClosure n1 n2 of
  ExIntro n3 p -> ExIntro (S' n3) (PSucc n1 n2 n3 p)

-- 定理 2.4 加法可換律

plusComm :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus n2 n1 n3
plusComm Z' n2 _ (PZero _) = plusZero n2
plusComm (S' n1) n2 _ (PSucc _ _ n3 p) = case plusComm n1 n2 n3 p of
  p' -> plusSucc n2 n1 n3 p'

succPlus :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus (S n1) n2 (S n3)
succPlus = PSucc
plusSucc :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus n1 (S n2) (S n3)
plusSucc Z' n2    _ (PZero _) = PZero (S' n2)
plusSucc (S' n1) n2 (S' n3) (PSucc _ _ _ j) 
  = case plusSucc n1 n2 n3 j of
      j'@(PSucc _ _ _ _) -> PSucc n1 (S' n2) (S' n3) j'

-- 定理 2.5 加法結合律

newtype PlusAssocR n1 n2 n3 n5 n6 = PlusAssocR (Plus n2 n3 n6,Plus n1 n6 n5)

plusAssocR :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4 -> Nat' n5
           -> Plus n1 n2 n4 -> Plus n4 n3 n5
           -> Exists Nat' (PlusAssocR n1 n2 n3 n5)
plusAssocR Z' n2 n3 _ n5 (PZero _) k = case plusClosure n2 n3 of
  ExIntro n6 j -> ExIntro n6 (PlusAssocR (j,k'))
                    where k' = case plusUnique n2 n3 n5 n6 k j of
                                 Refl -> PZero n6
plusAssocR (S' _) _ _ _ _ (PSucc n1 n2 n4 j) (PSucc _ n3 n5 k) = case plusAssocR n1 n2 n3 n4 n5 j k of
  ExIntro n6 (PlusAssocR (j',k')) -> ExIntro n6 (PlusAssocR (j',PSucc n1 n6 n5 k'))

newtype PlusAssocL n1 n2 n3 n5 n6 = PlusAssocL (Plus n1 n2 n6,Plus n6 n3 n5)

plusAssocL :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4 -> Nat' n5
            -> Plus n2 n3 n4 -> Plus n1 n4 n5
            -> Exists Nat' (PlusAssocL n1 n2 n3 n5)
plusAssocL n1 n2 n3 n4 n5 p1 p2 = case plusAssocR n3 n2 n1 n4 n5 (plusComm n2 n3 n4 p1) (plusComm n1 n4 n5 p2) of
  ExIntro n6 (PlusAssocR (p5,p6)) -> ExIntro n6 (PlusAssocL (plusComm n2 n1 n6 p5, plusComm n3 n6 n5 p6))

-- 定理 2.6 乗法唯一性

timesUnique :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4
            -> Times n1 n2 n3 -> Times n1 n2 n4
            -> n3 :=: n4
timesUnique Z' _ _ _ (TZero _) (TZero _) = Refl
timesUnique (S' n1) n2 n3 n4 (TSucc _ _ n n3' j j') (TSucc _ _ n' n4' k k')
  = case timesUnique n1 n2 n n' j k of
      Refl -> plusUnique n2 n n3' n4' j' k'

-- 定理 2.7 乗法閉包性
-- | 乗法の閉包性

timesClosure :: Nat' n1 -> Nat' n2 -> Exists Nat' (Times n1 n2)
timesClosure Z' n2 = ExIntro Z' (TZero n2)
timesClosure (S' n1) n2
 = case timesClosure n1 n2 of
     ExIntro n3 t -> case plusClosure n2 n3 of
       ExIntro n4 p -> ExIntro n4 (TSucc n1 n2 n3 n4 t p)

-- 定理 2.8 乗法零元

-- | 左零元 
leftZero :: Nat' n -> Times Z n Z
leftZero = TZero

-- | 右零元
rightZero :: Nat' n -> Times n Z Z
rightZero Z'     = TZero Z'
rightZero (S' n) = TSucc n Z' Z' Z' (rightZero n)  (PZero Z')

-- 定理 2.9 乗法交換律
-- | 乗法交換律

timesComm :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Times n1 n2 n3 -> Times n2 n1 n3
timesComm Z'      n2 _  (TZero _)              = rightZero n2
timesComm (S' n1) n2 n3 (TSucc _ _ n4 _ t1 p1) = timesSucc n2 n1 n4 n3 (timesComm n1 n2 n4 t1) p1

succTimes :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4 -> Times n1 n2 n3 -> Plus n2 n3 n4 -> Times (S n1) n2 n4
succTimes = TSucc

timesSucc :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4 -> Times n1 n2 n3 -> Plus n1 n3 n4 -> Times n1 (S n2) n4
timesSucc Z' n2 _  _ (TZero _) (PZero _) = TZero (S' n2)
timesSucc (S' n1) n2 n3 (S' n4) (TSucc _ _ n5 _ t1 p1) (PSucc _ _ _ p2) = case plusClosure n1 n5 of
  ExIntro n6 p3 -> case plusAssocL n1 n2 n5 n3 n4 p1 p2 of
    ExIntro n7 (PlusAssocL (p4,p5)) -> case plusAssocR n2 n1 n5 n7 n4 (plusComm n1 n2 n7 p4) p5 of
      ExIntro n8 (PlusAssocR (p7,p8)) -> case plusUnique n1 n5 n6 n8 p3 p7 of
        Refl -> TSucc n1 (S' n2) n6 (S' n4) (timesSucc n1 n2 n5 n6 t1 p3) (PSucc n2 n6 n4 p8)

-- 定理 2.10 乗法結合律

newtype TimesAssocR n1 n2 n3 n5 n6 = TimesAssocR (Times n2 n3 n6,Times n1 n6 n5)

timesAssocR :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4 -> Nat' n5
            -> Times n1 n2 n4 -> Times n4 n3 n5
            -> Exists Nat' (TimesAssocR n1 n2 n3 n5)
timesAssocR Z' n2 n3 _ _ (TZero _) (TZero _) = case timesClosure n2 n3 of
  ExIntro n6 t1 -> ExIntro n6 (TimesAssocR (t1,TZero n6))
timesAssocR (S' n1) n2 n3 n4 n5 (TSucc _ _ n6 _ t2 p2) t1 = case timesClosure n6 n3 of
  ExIntro n7 t3 -> case timesAssocR n1 n2 n3 n6 n7 t2 t3 of
    ExIntro n8 (TimesAssocR (t41,t42)) -> case timesDistribL n3 n2 n6 n4 n5 p2 (timesComm n4 n3 n5 t1) of
      ExIntro2 (Both (n9,n10)) (DistribL (t51,t52,p5)) -> case timesUnique n2 n3 n8 n9 t41 (timesComm n3 n2 n9 t51) of
        Refl -> case timesUnique n6 n3 n7 n10 t3 (timesComm n3 n6 n10 t52) of
          Refl -> ExIntro n8 (TimesAssocR (t41,TSucc n1 n8 n7 n5 t42 p5))

newtype TimesAssocL n1 n2 n3 n5 n6 = TimesAssocL (Times n1 n2 n6,Times n6 n3 n5)

timesAssocL :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4 -> Nat' n5
            -> Times n2 n3 n4 -> Times n1 n4 n5
            -> Exists Nat' (TimesAssocL n1 n2 n3 n5)
timesAssocL n1 n2 n3 n4 n5 t1 t2 = case timesAssocR n3 n2 n1 n4 n5 (timesComm n2 n3 n4 t1) (timesComm n1 n4 n5 t2) of
  ExIntro n6 (TimesAssocR (t3,t4)) -> ExIntro n6 (TimesAssocL (timesComm n2 n1 n6 t3,timesComm n3 n6 n5 t4))

-- 左分配律

newtype Both m n = Both (Nat' m, Nat' n)
newtype DistribL n1 n2 n3 n4 n5 n6 = DistribL (Times n1 n2 n5, Times n1 n3 n6, Plus n5 n6 n4)

timesDistribL :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4 -> Nat' n5
              -> Plus n2 n3 n4 -> Times n1 n4 n5
              -> Exists2 Both (DistribL n1 n2 n3 n5)
timesDistribL Z'      n2 n3 _  _  _  (TZero _) = ExIntro2 (Both (Z',Z')) (DistribL (TZero n2, TZero n3, PZero Z'))
timesDistribL (S' n1) n2 n3 n4 n5 p0 (TSucc _ _ n6 _ t1 p1) = case timesDistribL n1 n2 n3 n4 n6 p0 t1 of
  ExIntro2 (Both (n7,n8)) (DistribL (t21,t22,p2)) -> case plusAssocL n4 n7 n8 n6 n5 p2 p1 of
    ExIntro n9 (PlusAssocL (p31,p32)) -> case plusAssocR n3 n2 n7 n4 n9 (plusComm n2 n3 n4 p0) p31 of
      ExIntro n10 (PlusAssocR (p41,p42)) -> case plusAssocR n10 n3 n8 n9 n5 (plusComm n3 n10 n9 p42) p32 of
        ExIntro n11 (PlusAssocR (p51,p52))
          -> ExIntro2 (Both (n10,n11)) (DistribL (TSucc n1 n2 n7 n10 t21 p41,TSucc n1 n3 n8 n11 t22 p51,p52))

