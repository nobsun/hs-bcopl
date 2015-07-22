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

cong :: n :=: n' -> S n :=: S n'
cong j = case j of Refl -> Refl

posPZero :: Plus Z n n' -> n :=: n'
posPZero (PZero _) = Refl

-- ---------------------------------------------

theorem0201 :: Nat' n -> (Plus Z n n, Plus n Z n)
theorem0201 n = (leftUnit n, rightUnit n)

leftUnit  :: Nat' n -> Plus Z n n
leftUnit = PZero

rightUnit :: Nat' n -> Plus n Z n
rightUnit Z'     = PZero Z'
rightUnit (S' n) = case rightUnit n of
  hypothesis -> PSucc n Z' n hypothesis

pUnitZero  :: Nat' n -> (Plus Z n n, Plus n Z n)
pUnitZero  =  theorem0201

theorem0202 :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4
           -> Plus n1 n2 n3 -> Plus n1 n2 n4
           -> n3 :=: n4
theorem0202 Z' _ _ _ j j' = Trans (Sym (posPZero j)) (posPZero j')
theorem0202 (S' n1) n2 (S' n3) (S' n4) (PSucc _ _ _ j) (PSucc _ _ _ j')
  = cong (theorem0202 n1 n2 n3 n4 j j')

theorem0203 :: Nat' n1 -> Nat' n2 -> Plus n1 n2 n3 -> Nat' n3
theorem0203 Z' n2         (PZero _) = n2
theorem0203 (S' n1) n2 (PSucc _ _ _ j) 
  = case theorem0203 n1 n2 j of n3 -> S' n3

plus :: Nat' n1 -> Nat' n2 -> Plus n1 n2 n3 -> Nat' n3
plus = theorem0203

theorem0204 :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus n2 n1 n3
theorem0204 Z' n2 _ (PZero _) = rightUnit n2
theorem0204 (S' n1) Z' (S' n3) (PSucc _ _ _ j)
  = case theorem0204 n1 Z' n3 j of
      PZero _        -> leftUnit (S' n1)
theorem0204 (S' n1) (S' n2) (S' n3) (PSucc _ _ _ j)
  = case theorem0204 n1 (S' n2) n3 j of
      j' -> rightInc (S' n2) n1 n3 j'
      
leftInc :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus (S n1) n2 (S n3)
leftInc = PSucc

rightInc :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus n1 (S n2) (S n3)
rightInc Z' n2    _ (PZero _) = PZero (S' n2)
rightInc (S' n1) n2 (S' n3) (PSucc _ _ _ j) 
  = case rightInc n1 n2 n3 j of
      j'@(PSucc _ _ _ _) -> PSucc n1 (S' n2) (S' n3) j'

theorem0205 :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4 -> Nat' n5
            -> Plus n1 n2 n4 -> Plus n4 n3 n5
            -> Plus n2 n3 n6 -> Plus n1 n6 n5
            -> Nat' n6
theorem0205 Z' n2 n3 n4 n5 (PZero _) j j' (PZero _)
  = theorem0203 n2 n3 j
theorem0205 (S' n1) n2 n3 n4 n5 (PSucc _ _ _ j) (PSucc _ _ _ j') k (PSucc _ _ _ k')
  = theorem0205 n1 n2 n3 n4' n5' j j' k k'
    where n4' = theorem0203 n1 n2 j
          n5' = theorem0203 n4' n3 j'

theorem0206 :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4
           -> Times n1 n2 n3 -> Times n1 n2 n4
           -> n3 :=: n4
theorem0206 Z' _ _ _ (TZero _) (TZero _) = Refl
theorem0206 (S' n1) n2 n3 n4 (TSucc _ _ n n3' j j') (TSucc _ _ n' n4' k k')
  = case theorem0206 n1 n2 n n' j k of
      Refl -> theorem0202 n2 n n3' n4' j' k'

theorem0207 :: Nat' n1 -> Nat' n2 -> Times n1 n2 n3 -> Nat' n3
theorem0207 Z' n2         (TZero _) = Z'
theorem0207 (S' n1) n2 (TSucc _ _ _ _ t p) 
  = case theorem0207 n1 n2 t of n3 -> theorem0203 n2 n3 p

theorem0208 :: Nat' n -> (Times Z n Z, Times n Z Z)
theorem0208 n = (leftZero n, rightZero n)

leftZero :: Nat' n -> Times Z n Z
leftZero = TZero

rightZero :: Nat' n -> Times n Z Z
rightZero Z'     = TZero Z'
rightZero (S' n) = case rightZero n of
  hypothesis -> TSucc n Z' Z' Z' hypothesis (PZero Z')

{-
theorem0209 :: Nat' n1 -> Nat' n2 -> Nat' n3
            -> Times n1 n2 n3 -> Times n2 n1 n3
theorem0209 n1 Z'       Z' _       = leftZero n1
theorem0209 Z' (S' n2) _ (TZero _) = rightZero (S' n2)
theorem0209 (S' n1) (S' n2) _ (TSucc _ _ n3 _ j _)
  = case theorem0209 n1 (S' n2) n3 j of
      TSucc _ _ n4 _ j' _ -> case theorem0209 n2 n1 n4 j' of
        h -> undefined

lemma0209 :: Nat' n1 -> Nat' n2 -> Nat' n3
          -> Plus (S n1) n2 n3 -> Plus n1 (S n2) n3
lemma0209 = undefined

                                    Times n2 n1 n4
                                    Times n1 n2 n4
                                    Times (S n1) n2 n3'
                                    Times n2 (S n1) n3'
                                    Times (S n2) (S n1) n3


    (j+1) * (k+1) 
    ~~~~~~~~~~~~~       TSucc
--> j*(k+1) + (k+1)     
    ~~~~~~~             hypo
--> (k+1)*j + (k+1)     
    ~~~~~~~             TSucc
--> (k*j + j) + (k+1)   
    ~~~~~~~~~~~~~~~~~   p-assoc
--> k*j + (j+(k+1))    
    ~~~                 hypo
--> j*k + (j+(k+1))     
           ~~~~~~~      p-comm
--> j*k + ((k+1)+j)
          ~~~~~~~~~     lemma     
--> j*k + (k+(j+1))
    ~~~~~~~~~~~~~~~     p-assoc
--> (j*k + k) + (j+1)
    ~~~~~~~~~           TSucc
--> (j+1)*k  + (j+1)
    ~~~~~~~             hypo
--> k*(j+1) + j+1
    ~~~~~~~~~~~~~       TSucc
--> (k+1) * (j+1)

-}
