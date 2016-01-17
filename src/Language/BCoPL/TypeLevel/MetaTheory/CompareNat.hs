{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE EmptyCase #-}
module Language.BCoPL.TypeLevel.MetaTheory.CompareNat where

import Language.BCoPL.TypeLevel.Peano
import Language.BCoPL.TypeLevel.CompareNat

-- | 定理 2.11 (CompareNat1: 0 < 1+a)

zeroLtSucc1 :: Nat' n -> LessThan1 Z (S n)
zeroLtSucc1 n = case n of
  Z'    -> LSucc1 Z'
  S' n' -> LTrans1 Z' n (S' n) (zeroLtSucc1 n') (LSucc1 n)

-- | 定理 2.11 (CompareNat2: 0 < 1+a)

zeroLtSucc2 :: Nat' n -> LessThan2 Z (S n)
zeroLtSucc2 = LZero2

-- | 定理 2.11 (CompareNat3: 0 < 1+a)

zeroLtSucc3 :: Nat' n -> LessThan3 Z (S n)
zeroLtSucc3 n = case n of
  Z'    -> LSucc3 Z'
  S' n' -> LSuccR3 Z' n (zeroLtSucc3 n')

-- | 定理 2.12 (CompareNat1: 1+a < 1+b => a < b)

ltPred1 :: Nat' n1 -> Nat' n2 -> LessThan1 (S n1) (S n2) -> LessThan1 n1 n2
ltPred1 n1 n2 lt = case lt of
  LSucc1 _ -> LSucc1 n1
  LTrans1 _ n3 _ lt1 lt2 -> LTrans1 n1 (S' n1) n2 (LSucc1 n1) (lemma1 (S' n1) n3 n2 lt1 lt2)

lemma1 :: Nat' n1 -> Nat' n2 -> Nat' n3
       -> LessThan1 n1 n2 -> LessThan1 n2 (S n3)
       -> LessThan1 n1 n3
lemma1 n1 n2 n3 lt1 lt2 = case lt2 of
  LSucc1  _ -> lt1
  LTrans1 _ n4 _ lt3 lt4 -> LTrans1 n1 n2 n3 lt1 (lemma1 n2 n4 n3 lt3 lt4)
   
-- | 定理 2.12 (CompareNat2: 1+a < 1+b => a < b)

ltPred2 :: Nat' n1 -> Nat' n2 -> LessThan2 (S n1) (S n2) -> LessThan2 n1 n2
ltPred2 n1 n2 lt = case lt of
  LSuccSucc2 _ _ lt' -> lt'
  pat                -> case pat of {}

-- | 定理 2.12 (CompareNat3: 1+a < 1+b => a < b)

ltPred3 :: Nat' n1 -> Nat' n2 -> LessThan3 (S n1) (S n2) -> LessThan3 n1 n2
ltPred3 n1 n2 lt = case lt of
  LSucc3 _  -> LSucc3 n1
  LSuccR3 n1' n2' lt' -> lemma3 n1 n1' n2 (LSucc3 n1) lt'

lemma3 :: Nat' n1 -> Nat' n2 -> Nat' n3
       -> LessThan3 n1 n2 -> LessThan3 n2 n3
       -> LessThan3 n1 n3
lemma3 n1 n2 n3 lt1 lt2 = case lt2 of
  LSucc3  _ -> LSuccR3 n1 n2 lt1
  LSuccR3 _ n4 lt3 -> lemma3 n1 n4 n3 (lemma3 n1 n2 n4 lt1 lt3) (LSucc3 n4)

-- 定理 2.13
-- | 定理 2.13 (CompareNat1: a < b, b < c => a < c)
trans1 :: Nat' n1 -> Nat' n2 -> Nat' n3
       -> LessThan1 n1 n2 -> LessThan1 n2 n3
       -> LessThan1 n1 n3
trans1 = LTrans1

-- | 定理 2.13 (CompareNat2: a < b, b < c => a < c)
trans2 :: Nat' n1 -> Nat' n2 -> Nat' n3
       -> LessThan2 n1 n2 -> LessThan2 n2 n3
       -> LessThan2 n1 n3
trans2 n1 n2 n3 lt1 lt2 = case lt2 of
  LSuccSucc2 n4 n5 lt3 -> case lt1 of
    LZero2 _              -> LZero2 n5
    LSuccSucc2 n6 _ lt4     -> LSuccSucc2 n6 n5 (trans2 n6 n4 n5 lt4 lt3)
  pat                  -> case pat of {}

-- | 定理 2.13 (CompareNat3: a < b, b < c => a < c)
trans3 :: Nat' n1 -> Nat' n2 -> Nat' n3
       -> LessThan3 n1 n2 -> LessThan3 n2 n3
       -> LessThan3 n1 n3
trans3 = lemma3

-- | 定理 2.14

eqv13 :: Nat' n1 -> Nat' n2 -> LessThan1 n1 n2 -> LessThan3 n1 n2
eqv13 n1 n2 lt1 = case lt1 of
  LSucc1 _ -> LSucc3 n1
  LTrans1 _ n3 _ lt2 lt3 -> trans3 n1 n3 n2 (eqv13 n1 n3 lt2) (eqv13 n3 n2 lt3)

eqv32 :: Nat' n1 -> Nat' n2 -> LessThan3 n1 n2 -> LessThan2 n1 n2
eqv32 n1 n2 lt1 = case lt1 of
  LSucc3 _ -> case n1 of
    Z'       -> LZero2 n1
    S' n1'   -> LSuccSucc2 n1' n1 (eqv32 n1' n1 (LSucc3 n1'))
  LSuccR3 _ n3 lt2 -> trans2 n1 n3 n2 (eqv32 n1 n3 lt2) (eqv32 n3 n2 (LSucc3 n3))

eqv21 :: Nat' n1 -> Nat' n2 -> LessThan2 n1 n2 -> LessThan1 n1 n2
eqv21 n1 n2 lt1 = case lt1 of
  LZero2 n3 -> case n3 of
    Z'        -> LSucc1 n3
    S' n4     -> trans1 n1 n3 n2 (eqv21 n1 n3 (LZero2 n4)) (LSucc1 n3)
  LSuccSucc2 n5 n6 lt2 -> succSucc1 n5 n6 (eqv21 n5 n6 lt2)

succSucc1 :: Nat' n1 -> Nat' n2 -> LessThan1 n1 n2 -> LessThan1 (S n1) (S n2)
succSucc1 n1 n2 lt = case lt of
  LSucc1 _                -> LSucc1 n2
  LTrans1 _ n3 _ lt' lt'' -> LTrans1 (S' n1) (S' n3) (S' n2) (succSucc1 n1 n3 lt') (succSucc1 n3 n2 lt'')
