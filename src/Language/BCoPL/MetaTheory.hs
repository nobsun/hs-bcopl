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
{-
plusClosure :: Nat' n1 -> Nat' n2 -> n3 :=: (n1 :+ n2) -> Plus n1 n2 n3
plusClosure Z' n2 Refl      = PZero n2
plusClosure (S' n1) n2 Refl = PSucc n1 n2 (n1 :+: n2) (plusClosure n1 n2 Refl)

plusClosure' :: Nat' n1 -> Nat' n2 -> (Nat' (n1 :+ n2), Nat' (n1 :+ n2) -> Plus n1 n2 (n1 :+ n2))
plusClosure' Z' n2 =  (n2, PZero)
plusClosure' (S' n1) n2 = case plusClosure' n1 n2 of
  (n3, j) -> (S' n3, \ (S' n') -> PSucc n1 n2 n' (j n'))

plusConstruct :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> n3 :=: (n1 :+ n2)
plusConstruct Z' _ _ (PZero _)              = Refl
plusConstruct (S' n1) n2 _ (PSucc _ _ n3 j) = Cong (plusConstruct n1 n2 n3 j)

-- 定理 2.4 加法可換律

plusComm :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus n2 n1 n3
plusComm Z' n2 _ (PZero _) = plusZero n2
plusComm (S' n1) Z' (S' n3) (PSucc _ _ _ j)
  = case plusComm n1 Z' n3 j of
      PZero _        -> zeroPlus (S' n1)
plusComm (S' n1) (S' n2) (S' n3) (PSucc _ _ _ j)
  = case plusComm n1 (S' n2) n3 j of
      j' -> plusSucc (S' n2) n1 n3 j'
      
succPlus :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus (S n1) n2 (S n3)
succPlus = PSucc

plusSucc :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus n1 (S n2) (S n3)
plusSucc Z' n2    _ (PZero _) = PZero (S' n2)
plusSucc (S' n1) n2 (S' n3) (PSucc _ _ _ j) 
  = case plusSucc n1 n2 n3 j of
      j'@(PSucc _ _ _ _) -> PSucc n1 (S' n2) (S' n3) j'

-- 定理 2.5 加法結合律

plusAssocR :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4 -> Nat' n5
           -> Plus n1 n2 n4 -> Plus n4 n3 n5
           -> n6 :=: (n2 :+ n3)
           -> (Plus n2 n3 n6, Plus n1 n6 n5)
plusAssocR Z' n2 n3 n4 n5 (PZero _) k Refl
  = (j',k')
    where
      j' = plusClosure n2 n3 Refl
      k' = case plusUnique n2 n3 n5 (n2 :+: n3) k j' of
             Refl -> PZero n5
plusAssocR (S' _) _ _ _ _ (PSucc n1 n2 n4 j) (PSucc _ n3 n5 k) Refl
  = case plusAssocR n1 n2 n3 n4 n5 j k Refl of
      (j',k') -> (j',PSucc n1 (n2 :+: n3) n5 k')

plusAssocL :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4 -> Nat' n5
           -> Plus n2 n3 n4 -> Plus n1 n4 n5
           -> n6 :=: (n1 :+ n2)
           -> (Plus n1 n2 n6, Plus n6 n3 n5)
plusAssocL Z' n2 n3 n4 n5 j (PZero _) Refl
  = (PZero n2,j)
plusAssocL (S' _) n2 n3 n4 _ j (PSucc n1 _ n5 k) Refl
  = case plusAssocL n1 n2 n3 n4 n5 j k Refl of
      (j',k') -> (PSucc n1 n2 (n1 :+: n2) j', PSucc (n1 :+: n2) n3 n5 k')

-- -- 定理 2.6 乗法唯一性

timesUnique :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4
            -> Times n1 n2 n3 -> Times n1 n2 n4
            -> n3 :=: n4
timesUnique Z' _ _ _ (TZero _) (TZero _) = Refl
timesUnique (S' n1) n2 n3 n4 (TSucc _ _ n n3' j j') (TSucc _ _ n' n4' k k')
  = case timesUnique n1 n2 n n' j k of
      Refl -> plusUnique n2 n n3' n4' j' k'
-- -}
{-
0201: unitOnPlus :: ∀n . Nat n → (0 plus n is n, n plus 0 is n)
      zeroPlus   :: ∀n . Nat n → 0 plus n is n
      plusZero   :: ∀n . Nat n → n plus 0 is n
      eqZeroPlus :: ∀n n' . Plus Z n n' → n :=: n'
      eqPlusZero :: ∀n n' . Plus n Z n' → n :=: n'
      succPlus :: ∀n1 n2 n3 . n1 plus n2 is n3 → n1' plus n2 is n3'
      plusSucc :: ∀n1 n2 n3 . n1 plus n2 is n3 → n1 plus n2' is n3'
0202: plusUnique :: ∀n1 n2 n3 n4 . n1 plus n2 is n3 -> n1 plus n2 is n4 → n3 ≡ n4
0203: plusClosure   :: ∀n1 n2 . n3 ≡ n1 + n2 → n1 plus n2 is n3
      plusConstruct :: ∀n1 n2 n3 . n1 plus n2 is n3 → n1 + n2 ≡ n3
0204: plusComm :: ∀n1 n2 n3 . n1 plus n2 is n3 → n2 plus n1 is n3
0205: plusAssocR :: ∀n1 n2 n3 n4 n5 . 
                    n1 plus n2 is n4 → n4 plus n3 is n5
                 → n6 ≡ n2 + n3
                 → (n2 plus n3 is n6, n1 plus n6 is n5)
      plusAssocL :: ∀n1 n2 n3 n4 n5 . 
                    n2 plus n3 is n4 → n1 plus n4 is n5
                 → n6 ≡ n1 + n2
                 → (n1 plus n2 is n6, n6 plus n3 is n5)
0206: timesUnique :: ∀n1 n2 n3 n4 . n1 times n2 is n3 → n1 times n2 is n4 → n3 ≡ n4
0207: timesClosure :: ∀n1 n2 . n3 ≡ n1 * n2 → n1 times n2 is n3
 -}
-- 定理 2.7 乗法閉包性
{-
timesClosure :: Nat' n1 -> Nat' n2 -> n3 :=: (n1 :* n2) -> Times n1 n2 n3
timesClosure Z' n2 Refl = TZero n2
timesClosure (S' n1) n2 Refl
 = case timesClosure n1 n2 Refl of
     TZero _ -> TSucc Z' n2 Z' n2 (TZero n2) (plusZero n2)
     j@(TSucc _ _ _ n4 _ k) -> TSucc n1 n2 n4 (S' n1 :*: n2) j k'
                               where 
                                 k' = undefined k
-- -}
-- -- 定理 2.8 乗法零元

-- theorem0208 :: Nat' n -> (Times Z n Z, Times n Z Z)
-- theorem0208 n = (leftZero n, rightZero n)

-- leftZero :: Nat' n -> Times Z n Z
-- leftZero = TZero

-- rightZero :: Nat' n -> Times n Z Z
-- rightZero Z'     = TZero Z'
-- rightZero (S' n) = case rightZero n of
--   hypothesis -> TSucc n Z' Z' Z' hypothesis (PZero Z')

-- commSucc :: Nat' n1 -> Nat' n2 -> Nat' n3
--          -> Plus (S n1) n2 n3 -> Plus n1 (S n2) n3
-- commSucc n1 n2 _ (PSucc _ _ n3 j) = plusSucc n1 n2 n3 j

-- 定理 2.9 乗法交換律

-- timesComm :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Times n1 n2 n3 -> Times n2 n1 n3
-- timesComm Z' n2 Z' _      = rightZero n2
-- timesComm (S' n1) Z' Z' _ = leftZero (S' n1)
-- timesComm (S' n1) (S' n2) n3 (TSucc _ _ m _ t p)  -- n1 * (S n2) = m by t, (S n2) + m = n3 by p
--   = case timesComm n1 (S' n2) m t of
--       TSucc _n2 _n1 m' _m t' p'                   -- n2 * n1 = m' by t', n1 + m' = m by p'
--         -> case plusAssocR m' n1 (S' n2) m n3 
--                 (plusComm n1 m' m p') (plusComm (S' n2) m n3 p) undefined undefined of
--              n6 {- n1 + (S n2) -} -> r
         
--        where
--          r  = TSucc n2 (S' n1) m0 n3 p0 t0
--          m0 = undefined
--          p0 = timesComm (S' n1) n2 m0 p1
--          t0 = undefined
--          p1 = undefined

-- {-
--     (j+1) * (k+1) 
--     ~~~~~~~~~~~~~       TSucc j (k+1) n3 n jt jp :: Times (j+1) (k+1) n where jp@(PSucc k n3 n-) :: Plus (k+1) n3 n 
-- --> j*(k+1) + (k+1)     
--     ~~~~~~~             hypo j (k+1) n3 jt :: Times (k+1) j n3 where jt :: Times  j (k+1) n3
-- --> (k+1)*j + (k+1)     
--     ~~~~~~~             TSucc k j n3' n3 jt' jp'
-- --> (k*j + j) + (k+1)   
--     ~~~~~~~~~~~~~~~~~   p-assoc n3
-- --> k*j + (j+(k+1))    
--     ~~~                 hypo
-- --> j*k + (j+(k+1))     
--           ~~~~~~~~~     p-comm
-- --> j*k + ((k+1)+j)
--           ~~~~~~~~~     lemma     
-- --> j*k + (k+(j+1))
--   h  ~~~~~~~~~~~~~~~     p-assoc
-- --> (j*k + k) + (j+1)
--     ~~~~~~~~~           jt' = TSucc j k n3' jt'' jp
-- --> (j+1)*k  + (j+1)
--     ~~~~~~~             hypo
-- --> k*(j+1) + j+1 = n4
--     ~~~~~~~~~~~~~             TSucc k (j+1) n3 jt jp where { n3 = k*(j+1); jt = hypo (j+1) k n3 jt' }
-- --> (k+1) * (j+1) = n4

-- TSucc k (j+1) m n jt jp
--   where
--     jt :: Times k (j+1) m
--     jt =  hypo (j+1) k m jt'
--     jp :: Plus (j+1) m n
--     jp =  PSucc j m _n jp'
  
--     jt' :: Times (j+1) k m
--     jt' =  TSucc j k _m m jt'' jp''
--     jp' :: Plus j m _n
--     jp' =  undefined


-- -}

-- {-
-- jt3
-- -----------------------------------------------
-- jt2 :: Times (j+1) k m = PSucc j k m1 m jt3 jp2
-- -----------------------------------------------
-- jt1 :: Times k (j+1) m = hypo (j+1) k m jt2        jp1 :: Plus (j+1) m n
-- ------------------------------------------------------------------------
--    jt0 :: Times (k+1) (j+1) n = TSucc k (j+1) m n jt1 jp1
-- -}
