{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE EmptyCase #-}
module Language.BCoPL.TypeLevel.MetaTheory.EvalNatExp where

import Language.BCoPL.TypeLevel.Peano
import Language.BCoPL.TypeLevel.Exp

import Language.BCoPL.TypeLevel.Equiv
import Language.BCoPL.TypeLevel.Exists
import Language.BCoPL.TypeLevel.EvalNatExp

import Language.BCoPL.TypeLevel.MetaTheory.Nat

-- | 定理 2.15 (Totality of evaluation)

total :: Exp' e -> Exists Nat' (EvalTo e)
total exp = case exp of
  ENat' n   -> ExIntro n (EConst n)
  e1 :＋: e2 -> case total e1 of
    ExIntro n1 ev1 -> case total e2 of
      ExIntro n2 ev2 -> case plusClosure n1 n2 of
        ExIntro n3 p   -> ExIntro n3 (EPlus e1 e2 n1 n2 n3 ev1 ev2 p)
  e1 :×: e2 -> case total e1 of
    ExIntro n1 ev1 -> case total e2 of
      ExIntro n2 ev2 -> case timesClosure n1 n2 of
        ExIntro n3 t   -> ExIntro n3 (ETimes e1 e2 n1 n2 n3 ev1 ev2 t)

-- | 定理 2.16 (Uniqueness of evaluation)

unique :: Exp' e -> Nat' n1 -> Nat' n2
       -> EvalTo e n1 -> EvalTo e n2
       -> n1 :=: n2
unique e n n' ev1 ev2 = case e of
  ENat' _ -> case ev1 of
    EConst _ -> case ev2 of
      EConst _ -> Refl
      pat      -> case pat of {}
    pat      -> case pat of {}
  e1 :＋: e2 -> case ev1 of
    EPlus _ _ n11 n21 _ ev11 ev21 p -> case ev2 of
      EPlus _ _ n11' n21' _ ev11' ev21' p' -> case unique e1 n11 n11' ev11 ev11' of
        Refl -> case unique e2 n21 n21' ev21 ev21' of
          Refl -> plusUnique n11 n21 n n' p p'
      pat -> case pat of {}
    pat -> case pat of {}
  e1 :×: e2 -> case ev1 of
    ETimes _ _ n11 n21 _ ev11 ev21 t -> case ev2 of
      ETimes _ _ n11' n21' _ ev11' ev21' t' -> case unique e1 n11 n11' ev11 ev11' of
        Refl -> case unique e2 n21 n21' ev21 ev21' of
          Refl -> timesUnique n11 n21 n n' t t'
      pat -> case pat of {}
    pat -> case pat of {}

-- | 定理 2.17 (Commutativity of +)

commPlus :: Exp' e1 -> Exp' e2 -> Nat' n -> EvalTo (e1 :＋ e2) n -> EvalTo (e2 :＋ e1) n
commPlus e1 e2 n ev = case ev of
  EPlus _ _ n1 n2 n3 ev1 ev2 p -> EPlus e2 e1 n2 n1 n3 ev2 ev1 (plusComm n1 n2 n3 p)
  pat                          -> case pat of {}

-- | 定理 2.18 (Associativity of +)

assocRPlus :: Exp' e1 -> Exp' e2 -> Exp' e3 -> Nat' n -> EvalTo ((e1 :＋ e2) :＋ e3) n -> EvalTo (e1 :＋ (e2 :＋ e3)) n
assocRPlus e1 e2 e3 n ev = case ev of
  EPlus e4 _ n4 n3 n5 ev4 ev3 p -> case ev4 of
    EPlus _ _ n1 n2 _ ev1 ev2 p'  -> case plusAssocR n1 n2 n3 n4 n5 p' p of
      ExIntro n6 (PlusAssocR (q,q')) -> EPlus e1 (e2 :＋: e3) n1 n6 n5 ev1 (EPlus e2 e3 n2 n3 n6 ev2 ev3 q) q'
    pat                           -> case pat of {}
  pat                           -> case pat of {}

-- | 定理 2.19 (Commutativity of *)

commTimes :: Exp' e1 -> Exp' e2 -> Nat' n -> EvalTo (e1 :× e2) n -> EvalTo (e2 :× e1) n
commTimes e1 e2 n ev = case ev of
  ETimes _ _ n1 n2 n3 ev1 ev2 t -> ETimes e2 e1 n2 n1 n3 ev2 ev1 (timesComm n1 n2 n3 t)
  pat                           -> case pat of {}

-- | 定理 2.20 (Associativity of *)

assocRTimes :: Exp' e1 -> Exp' e2 -> Exp' e3 -> Nat' n -> EvalTo ((e1 :× e2) :× e3) n -> EvalTo (e1 :× (e2 :× e3)) n
assocRTimes e1 e2 e3 n ev = case ev of
  ETimes e4 _ n4 n3 n5 ev4 ev3 t -> case ev4 of
    ETimes _ _ n1 n2 _ ev1 ev2 t'  -> case timesAssocR n1 n2 n3 n4 n5 t' t of
      ExIntro n6 (TimesAssocR (u,u')) -> ETimes e1 (e2 :×: e3) n1 n6 n5 ev1 (ETimes e2 e3 n2 n3 n6 ev2 ev3 u) u'
    pat                           -> case pat of {}
  pat                           -> case pat of {}

