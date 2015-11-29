{-# LANGUAGE RankNTypes #-}
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
module Language.BCoPL.MetaTheory where

import Control.Applicative ((<*>))

import Language.BCoPL.Peano
import Language.BCoPL.CompareNat
import Language.BCoPL.Nat

import Language.BCoPL.Equiv
import Language.BCoPL.Exists

-- ---------------------------------------------

-- 定理 2.1 加法単位元

zeroPlus  :: Nat' n -> Plus Z n n              -- 公理 P-Zero
zeroPlus = PZero

plusZero :: Nat' n -> Plus n Z n
plusZero Z'     = PZero Z'
plusZero (S' n) = PSucc n Z' n (plusZero n)

unitZeroPlus  :: Nat' n -> (Plus Z n n, Plus n Z n)
unitZeroPlus n = (zeroPlus n, plusZero n)

eqZeroPlus :: Nat' n -> Nat' n' -> Plus Z n n' -> n :=: n'
eqZeroPlus _ _ (PZero _) = Refl

eqPlusZero :: Nat' n -> Nat' n' -> Plus n Z n' -> n :=: n'
eqPlusZero Z' n' (PZero _)  = eqZeroPlus Z' n' (PZero n')
eqPlusZero (S' n) _ (PSucc _ _ n' j) = Cong (eqPlusZero n n' j)

-- 定理 2.2 加法唯一性

plusUnique :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4
           -> Plus n1 n2 n3 -> Plus n1 n2 n4
           -> n3 :=: n4
plusUnique Z' n2 n3 n4 j@(PZero _) k@(PZero _) 
  = Trans (Sym (eqZeroPlus n2 n3 j)) (eqZeroPlus n2 n4 k)
plusUnique (S' n1) n2 (S' n3) (S' n4) (PSucc _ _ _ j) (PSucc _ _ _ j')
  = Cong (plusUnique n1 n2 n3 n4 j j')

-- 定理 2.3 加法閉包性

plusClosure :: Nat' n1 -> Nat' n2 -> Exists Nat' (Plus n1 n2)
plusClosure Z' n2       = ExIntro n2 (PZero n2)
plusClosure (S' n1) n2 = case plusClosure n1 n2 of
  ExIntro n3 p -> ExIntro (S' n3) (PSucc n1 n2 n3 p)

