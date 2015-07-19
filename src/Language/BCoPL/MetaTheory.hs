{-# LANGUAGE RankNTypes #-}
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
module Language.BCoPL.MetaTheory where

import Language.BCoPL.Peano
import Language.BCoPL.CompareNat
import Language.BCoPL.Nat

import Language.BCoPL.Equiv

baseCase :: Z :=: Z
baseCase =  Refl

inductiveCase :: n :=: n' -> S n :=: S n'
inductiveCase j = case j of Refl -> Refl

posPZero :: Plus Z n n' -> n :=: n'
posPZero (PZero _) = Refl

-- ---------------------------------------------

theorem0201 :: Nat' n -> (Plus Z n n, Plus n Z n)
theorem0201 n = (leftUnit n, rightUnit n)

leftUnit  :: Nat' n -> Plus Z n n
rightUnit :: Nat' n -> Plus n Z n
leftUnit = PZero
rightUnit Z'     = PZero Z'
rightUnit (S' n) = case rightUnit n of
  hypothesis -> PSucc n Z' n hypothesis

theorem0202 :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4
           -> Plus n1 n2 n3 -> Plus n1 n2 n4
           -> n3 :=: n4
theorem0202 Z' _ _ _ j j' = Trans (Sym (posPZero j)) (posPZero j')
theorem0202 (S' n1) n2 (S' n3) (S' n4) (PSucc _ _ _ j) (PSucc _ _ _ j')
  = inductiveCase (theorem0202 n1 n2 n3 n4 j j')

theorem0203 :: Nat' n1 -> Nat' n2 -> Plus n1 n2 n3 -> Nat' n3
theorem0203 Z' n2 (PZero _) = n2
theorem0203 (S' n1) n2 (PSucc _ _ _ j) 
  = case theorem0203 n1 n2 j of n3 -> S' n3

theorem0204 :: Nat' n1 -> Nat' n2 -> Nat' n3
           -> Plus n1 n2 n3 -> Plus n2 n1 n3
theorem0204 Z' n2 _ (PZero _) = rightUnit n2
theorem0204 (S' n1) Z' (S' n3) (PSucc _ _ _ j)
  = case theorem0204 n1 Z' n3 j of
      PZero _        -> leftUnit (S' n1)
theorem0204 (S' n1) (S' n2) (S' n3) (PSucc _ _ _ j)
  = case theorem0204 n1 (S' n2) n3 j of
      j' -> rightInc (S' n2) n1 n3 j'
      
rightInc :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus n1 (S n2) (S n3)
rightInc Z' n2    _ (PZero _) = PZero (S' n2)
rightInc (S' n1) n2 (S' n3) (PSucc _ _ _ j) 
  = case rightInc n1 n2 n3 j of
      j'@(PSucc _ _ _ _) -> PSucc n1 (S' n2) (S' n3) j'
          

