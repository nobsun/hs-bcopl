{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyCase #-}
module Language.BCoPL.TypeLevel.MetaTheory.ReduceNatExp where

import Language.BCoPL.TypeLevel.Peano
import Language.BCoPL.TypeLevel.Nat

import Language.BCoPL.TypeLevel.Equiv
import Language.BCoPL.TypeLevel.Exists

import Language.BCoPL.TypeLevel.Exp
import Language.BCoPL.TypeLevel.ReduceNatExp

import Language.BCoPL.TypeLevel.MetaTheory.Nat

newtype BothExp e1 e2 = BothExp (Exp' e1, Exp' e2)
newtype PlusExp  e e1 e2 = PlusExp  (e :=: (e1 :＋ e2))
newtype TimesExp e e1 e2 = TimesExp (e :=: (e1 :× e2))
newtype PlusExpδ e n1 n2 = PlusExpδ (e :=: (ENat n1 :＋ ENat n2))
newtype TimesExpδ e n1 n2 = TimesExpδ (e :=: (ENat n1 :× ENat n2))
newtype NatExp e n = NatExp (e :=: ENat n)

data NF (e :: Exp) where
  ExpNat :: Exists Nat' (NatExp e) -> NF e

data Redex (e :: Exp) where
  ExpPlus  :: Exists2 BothExp (PlusExp e)  -> Redex e
  ExpTimes :: Exists2 BothExp (TimesExp e) -> Redex e

data Redexδ (e :: Exp) where
  ExpPlusδ :: Exists2 Both (PlusExpδ e) -> Redexδ e
  ExpTimesδ :: Exists2 Both (TimesExpδ e) -> Redexδ e

-- | 定理 2.21 (簡約の前進性)

progressive :: Exp' e -> Redex e -> Exists Exp' ((:--->) e)
progressive e r = case r of
  ExpPlus (ExIntro2 (BothExp(e1,e2)) (PlusExp Refl)) -> case e1 of
    ENat' n1 -> case e2 of
      ENat' n2 -> case plusClosure n1 n2 of
        ExIntro n3 p -> ExIntro (ENat' n3) (RPlus n1 n2 n3 p)
      e21 :＋: e22 -> case progressive e2 (ExpPlus (ExIntro2 (BothExp (e21,e22)) (PlusExp Refl))) of
        ExIntro e2' r2 -> ExIntro (e1 :＋: e2') (RPlusR e1 e2 e2' r2)
      e21 :×: e22 -> case progressive e2 (ExpTimes (ExIntro2 (BothExp (e21,e22)) (TimesExp Refl))) of
        ExIntro e2' r2 -> ExIntro (e1 :＋: e2') (RPlusR e1 e2 e2' r2)
    e11 :＋: e12 -> case progressive e1 (ExpPlus (ExIntro2 (BothExp (e11,e12)) (PlusExp Refl))) of
      ExIntro e1' r1 -> ExIntro (e1' :＋: e2) (RPlusL e1 e1' e2 r1)
    e11 :×: e12 -> case progressive e1 (ExpTimes (ExIntro2 (BothExp (e11,e12)) (TimesExp Refl))) of
      ExIntro e1' r1 -> ExIntro (e1' :＋: e2) (RPlusL e1 e1' e2 r1)
  ExpTimes (ExIntro2 (BothExp(e1,e2)) (TimesExp Refl)) -> case e1 of
    ENat' n1 -> case e2 of
      ENat' n2 -> case timesClosure n1 n2 of
        ExIntro n3 p -> ExIntro (ENat' n3) (RTimes n1 n2 n3 p)
      e21 :＋: e22 -> case progressive e2 (ExpPlus (ExIntro2 (BothExp (e21,e22)) (PlusExp Refl))) of
        ExIntro e2' r2 -> ExIntro (e1 :×: e2') (RTimesR e1 e2 e2' r2)
      e21 :×: e22 -> case progressive e2 (ExpTimes (ExIntro2 (BothExp (e21,e22)) (TimesExp Refl))) of
        ExIntro e2' r2 -> ExIntro (e1 :×: e2') (RTimesR e1 e2 e2' r2)
    e11 :＋: e12 -> case progressive e1 (ExpPlus (ExIntro2 (BothExp (e11,e12)) (PlusExp Refl))) of
      ExIntro e1' r1 -> ExIntro (e1' :×: e2) (RTimesL e1 e1' e2 r1)
    e11 :×: e12 -> case progressive e1 (ExpTimes (ExIntro2 (BothExp (e11,e12)) (TimesExp Refl))) of
      ExIntro e1' r1 -> ExIntro (e1' :×: e2) (RTimesL e1 e1' e2 r1)

-- | 定理 2.22 (簡約の合流性)

newtype Confluent e2 e3 e4 = Confluent (e2 :---> e4, e3 :---> e4)

confluent :: Exp' e1 -> Exp' e2 -> Exp' e3
          -> Redex e2 -> Redex e3
          -> e1 :---> e2 -> e1 :---> e3
          -> Exists Exp' (Confluent e2 e3)
confluent e1 e2 e3 rd2 rd3 r2 r3 = case redRedex e1 e2 r2 of
  ExpPlus (ExIntro2 (BothExp (e11,e12)) (PlusExp Refl)) -> case rd2 of
    ExpPlus (ExIntro2 (BothExp (_,_)) (PlusExp Refl))     -> case rd3 of
      ExpPlus (ExIntro2 (BothExp (_,_)) (PlusExp Refl))     -> case r2 of
        RPlusL _e11 e21 _e12 r21 -> case r3 of
          RPlusL _e11 e31 _e12 r31 -> case e21 of
            ENat' n21 -> case uniqueδReduction e11 e21 e31 (redδRedex e11 e21 r21 (ExpNat (ExIntro n21 (NatExp Refl)))) r21 r31 of
              Refl -> case e12 of
                ENat' n12 -> case plusClosure n21 n12 of
                  ExIntro n p -> ExIntro (ENat' n) (Confluent (RPlus n21 n12 n p, RPlus n21 n12 n p))
                e121 :＋: e122 -> case progressive e12 (ExpPlus (ExIntro2 (BothExp (e121,e122)) (PlusExp Refl))) of
                  ExIntro e12' r12' -> ExIntro (e21 :＋: e12') (Confluent (RPlusR e21 e12 e12' r12',RPlusR e21 e12 e12' r12'))
                e121 :×: e122 -> case progressive e12 (ExpTimes (ExIntro2 (BothExp (e121,e122)) (TimesExp Refl))) of
                  ExIntro e12' r12' -> ExIntro (e21 :＋: e12') (Confluent (RPlusR e21 e12 e12' r12',RPlusR e21 e12 e12' r12'))
            e211 :＋: e212 -> case e31 of
              e311 :＋: e312 -> case confluent e11 e21 e31 (ExpPlus (ExIntro2 (BothExp (e211,e212)) (PlusExp Refl))) (ExpPlus (ExIntro2 (BothExp (e311,e312)) (PlusExp Refl))) r21 r31 of
                ExIntro e41 (Confluent (r241,r341)) -> ExIntro (e41:＋:e12) (Confluent (RPlusL e21 e41 e12 r241,RPlusL e31 e41 e12 r341))
              pat -> case pat of {}
            e211 :×: e212 -> case e31 of
              e311 :×: e312 -> case confluent e11 e21 e31 (ExpTimes (ExIntro2 (BothExp (e211,e212)) (TimesExp Refl))) (ExpTimes (ExIntro2 (BothExp (e311,e312)) (TimesExp Refl))) r21 r31 of
                ExIntro e41 (Confluent (r241,r341)) -> ExIntro (e41:＋:e12) (Confluent (RPlusL e21 e41 e12 r241,RPlusL e31 e41 e12 r341))
              pat -> case pat of {}
          RPlusR _e11 _e12 e32 r32 -> ExIntro (e21:＋:e32) (Confluent (RPlusR e21 e12 e32 r32,RPlusL e11 e21 e32 r21))
          pat -> case pat of {}
        RPlusR _e11 _e12 e22 r22 -> case r3 of
          RPlusL _e11 e31 _e12 r31 -> ExIntro (e31:＋:e22) (Confluent (RPlusL e11 e31 e22 r31,RPlusR e31 e12 e22 r22))
          RPlusR _e11 _e12 e32 r32 -> case e22 of
            ENat' n22 -> case uniqueδReduction e12 e22 e32 (redδRedex e12 e22 r22 (ExpNat (ExIntro n22 (NatExp Refl)))) r22 r32 of
              Refl -> case e11 of
                ENat' n11 -> case plusClosure n11 n22 of
                  ExIntro n p -> ExIntro (ENat' n) (Confluent (RPlus n11 n22 n p, RPlus n11 n22 n p))
                e111 :＋: e112 -> case progressive e11 (ExpPlus (ExIntro2 (BothExp (e111,e112)) (PlusExp Refl))) of
                  ExIntro e11' r11' -> ExIntro (e11' :＋: e22) (Confluent (RPlusL e11 e11' e22 r11',RPlusL e11 e11' e22 r11'))
                e111 :×: e112 -> case progressive e11 (ExpTimes (ExIntro2 (BothExp (e111,e112)) (TimesExp Refl))) of
                  ExIntro e11' r11' -> ExIntro (e11' :＋: e22) (Confluent (RPlusL e11 e11' e22 r11',RPlusL e11 e11' e22 r11'))
            e221 :＋: e222 -> case e32 of
              e321 :＋: e322 -> case confluent e12 e22 e32 (ExpPlus (ExIntro2 (BothExp (e221,e222)) (PlusExp Refl))) (ExpPlus (ExIntro2 (BothExp (e321,e322)) (PlusExp Refl))) r22 r32 of
                ExIntro e42 (Confluent (r242,r342)) -> ExIntro (e11:＋:e42) (Confluent (RPlusR e11 e22 e42 r242,RPlusR e11 e32 e42 r342))
                pat -> case pat of {}
              pat -> case pat of {}
            e221 :×: e222 -> case e32 of
              e321 :×: e322 -> case confluent e12 e22 e32 (ExpTimes (ExIntro2 (BothExp (e221,e222)) (TimesExp Refl))) (ExpTimes (ExIntro2 (BothExp (e321,e322)) (TimesExp Refl))) r22 r32 of
                ExIntro e42 (Confluent (r242,r342)) -> ExIntro (e11:＋:e42) (Confluent (RPlusR e11 e22 e42 r242,RPlusR e11 e32 e42 r342))
                pat -> case pat of {}
              pat -> case pat of {}
          pat -> case pat of {}
        pat -> case pat of {}
      pat -> case pat of {}
    pat -> case pat of {}
  ExpTimes (ExIntro2 (BothExp (e11,e12)) (TimesExp Refl)) -> case rd2 of
    ExpTimes (ExIntro2 (BothExp (_,_)) (TimesExp Refl))     -> case rd3 of
      ExpTimes (ExIntro2 (BothExp (_,_)) (TimesExp Refl))     -> case r2 of
        RTimesL _e11 e21 _e12 r21 -> case r3 of
          RTimesL _e11 e31 _e12 r31 -> case e21 of
            ENat' n21 -> case uniqueδReduction e11 e21 e31 (redδRedex e11 e21 r21 (ExpNat (ExIntro n21 (NatExp Refl)))) r21 r31 of
              Refl -> case e12 of
                ENat' n12 -> case timesClosure n21 n12 of
                  ExIntro n p -> ExIntro (ENat' n) (Confluent (RTimes n21 n12 n p, RTimes n21 n12 n p))
                e121 :＋: e122 -> case progressive e12 (ExpPlus (ExIntro2 (BothExp (e121,e122)) (PlusExp Refl))) of
                  ExIntro e12' r12' -> ExIntro (e21 :×: e12') (Confluent (RTimesR e21 e12 e12' r12',RTimesR e21 e12 e12' r12'))
                e121 :×: e122 -> case progressive e12 (ExpTimes (ExIntro2 (BothExp (e121,e122)) (TimesExp Refl))) of
                  ExIntro e12' r12' -> ExIntro (e21 :×: e12') (Confluent (RTimesR e21 e12 e12' r12',RTimesR e21 e12 e12' r12'))
            e211 :＋: e212 -> case e31 of
              e311 :＋: e312 -> case confluent e11 e21 e31 (ExpPlus (ExIntro2 (BothExp (e211,e212)) (PlusExp Refl))) (ExpPlus (ExIntro2 (BothExp (e311,e312)) (PlusExp Refl))) r21 r31 of
                ExIntro e41 (Confluent (r241,r341)) -> ExIntro (e41:×:e12) (Confluent (RTimesL e21 e41 e12 r241,RTimesL e31 e41 e12 r341))
              pat -> case pat of {}
            e211 :×: e212 -> case e31 of
              e311 :×: e312 -> case confluent e11 e21 e31 (ExpTimes (ExIntro2 (BothExp (e211,e212)) (TimesExp Refl))) (ExpTimes (ExIntro2 (BothExp (e311,e312)) (TimesExp Refl))) r21 r31 of
                ExIntro e41 (Confluent (r241,r341)) -> ExIntro (e41:×:e12) (Confluent (RTimesL e21 e41 e12 r241,RTimesL e31 e41 e12 r341))
              pat -> case pat of {}
          RTimesR _e11 _e12 e32 r32 -> ExIntro (e21:×:e32) (Confluent (RTimesR e21 e12 e32 r32,RTimesL e11 e21 e32 r21))
          pat -> case pat of {}
        RTimesR _e11 _e12 e22 r22 -> case r3 of
          RTimesL _e11 e31 _e12 r31 -> ExIntro (e31:×:e22) (Confluent (RTimesL e11 e31 e22 r31,RTimesR e31 e12 e22 r22))
          RTimesR _e11 _e12 e32 r32 -> case e22 of
            ENat' n22 -> case uniqueδReduction e12 e22 e32 (redδRedex e12 e22 r22 (ExpNat (ExIntro n22 (NatExp Refl)))) r22 r32 of
              Refl -> case e11 of
                ENat' n11 -> case timesClosure n11 n22 of
                  ExIntro n p -> ExIntro (ENat' n) (Confluent (RTimes n11 n22 n p, RTimes n11 n22 n p))
                e111 :＋: e112 -> case progressive e11 (ExpPlus (ExIntro2 (BothExp (e111,e112)) (PlusExp Refl))) of
                  ExIntro e11' r11' -> ExIntro (e11' :×: e22) (Confluent (RTimesL e11 e11' e22 r11',RTimesL e11 e11' e22 r11'))
                e111 :×: e112 -> case progressive e11 (ExpTimes (ExIntro2 (BothExp (e111,e112)) (TimesExp Refl))) of
                  ExIntro e11' r11' -> ExIntro (e11' :×: e22) (Confluent (RTimesL e11 e11' e22 r11',RTimesL e11 e11' e22 r11'))
            e221 :＋: e222 -> case e32 of
              e321 :＋: e322 -> case confluent e12 e22 e32 (ExpPlus (ExIntro2 (BothExp (e221,e222)) (PlusExp Refl))) (ExpPlus (ExIntro2 (BothExp (e321,e322)) (PlusExp Refl))) r22 r32 of
                ExIntro e42 (Confluent (r242,r342)) -> ExIntro (e11:×:e42) (Confluent (RTimesR e11 e22 e42 r242,RTimesR e11 e32 e42 r342))
                pat -> case pat of {}
              pat -> case pat of {}
            e221 :×: e222 -> case e32 of
              e321 :×: e322 -> case confluent e12 e22 e32 (ExpTimes (ExIntro2 (BothExp (e221,e222)) (TimesExp Refl))) (ExpTimes (ExIntro2 (BothExp (e321,e322)) (TimesExp Refl))) r22 r32 of
                ExIntro e42 (Confluent (r242,r342)) -> ExIntro (e11:×:e42) (Confluent (RTimesR e11 e22 e42 r242,RTimesR e11 e32 e42 r342))
                pat -> case pat of {}
              pat -> case pat of {}
          pat -> case pat of {}
        pat -> case pat of {}
      pat -> case pat of {}
    pat -> case pat of {}

redRedex :: Exp' e -> Exp' e' -> e :---> e' -> Redex e
redRedex e e' rd = case rd of
  RPlus   n1 n2 _ _ -> ExpPlus (ExIntro2 (BothExp (ENat' n1,ENat' n2)) (PlusExp Refl))
  RTimes  n1 n2 _ _ -> ExpTimes (ExIntro2 (BothExp (ENat' n1,ENat' n2)) (TimesExp Refl))
  RPlusL  e1 _ e2 _ -> ExpPlus (ExIntro2 (BothExp (e1,e2)) (PlusExp Refl))
  RTimesL e1 _ e2 _ -> ExpTimes (ExIntro2 (BothExp (e1,e2)) (TimesExp Refl))
  RPlusR  e1 e2 _ _ -> ExpPlus (ExIntro2 (BothExp (e1,e2)) (PlusExp Refl))
  RTimesR e1 e2 _ _ -> ExpTimes (ExIntro2 (BothExp (e1,e2)) (TimesExp Refl))

redδRedex :: Exp' e -> Exp' e' -> (e :---> e') -> NF e' -> Redexδ e
redδRedex e e' r ne = case ne of
  ExpNat (ExIntro n (NatExp Refl)) -> case r of
    RPlus  n1 n2 _ _ -> ExpPlusδ  (ExIntro2 (Both (n1,n2)) (PlusExpδ Refl))
    RTimes n1 n2 _ _ -> ExpTimesδ (ExIntro2 (Both (n1,n2)) (TimesExpδ Refl))
    pat -> case pat of {}

uniqueδReduction :: Exp' e -> Exp' e1 -> Exp' e2 -> Redexδ e -> (e :---> e1) -> (e :---> e2) -> (e1 :=: e2)
uniqueδReduction e e1 e2 de r1 r2 = case de of
  ExpPlusδ (ExIntro2 (Both(n1,n2)) (PlusExpδ Refl)) -> case r1 of
    RPlus _ _ n3 p1 -> case r2 of
      RPlus _ _ n4 p2 -> case plusUnique n1 n2 n3 n4 p1 p2 of
        Refl -> Refl
      pat -> case pat of {}
    pat -> case pat of {}
  ExpTimesδ (ExIntro2 (Both(n1,n2)) (TimesExpδ Refl)) ->  case r1 of
    RTimes _ _ n3 t1 -> case r2 of
      RTimes _ _ n4 t2 -> case timesUnique n1 n2 n3 n4 t1 t2 of
        Refl -> Refl
      pat -> case pat of {}
    pat -> case pat of {}

-- | 定理 2.23 (決定性簡約の一意性)

uniqueDRed :: Exp' e -> Exp' e' -> Exp' e'' -> (e :-/-> e') -> (e :-/-> e'') -> (e' :=: e'')
uniqueDRed e e' e'' r' r'' = case dredRedex  e e' r' of
  ExpPlus (ExIntro2 (BothExp (e1,e2)) (PlusExp Refl)) -> case r' of
    DRPlus n1 n2 n3 p -> uniqueδDReduction e e' e'' (dredδRedex e e' r' (ExpNat (ExIntro n3 (NatExp Refl)))) r' r''
    DRPlusL e1 e1' e2 r1' -> case r'' of
      DRPlusL e1 e1'' e2 r1'' -> case uniqueDRed e1 e1' e1'' r1' r1'' of Refl -> Refl
      pat -> case pat of {}
    DRPlusR n1 e2 e2' r2' -> case r'' of
      DRPlusR n1 e2 e2'' r2'' -> case uniqueDRed e2 e2' e2'' r2' r2'' of Refl -> Refl
      pat -> case pat of {}
    pat -> case pat of {}
  ExpTimes (ExIntro2 (BothExp (e1,e2)) (TimesExp Refl)) -> case r' of
    DRTimes n1 n2 n3 p -> uniqueδDReduction e e' e'' (dredδRedex e e' r' (ExpNat (ExIntro n3 (NatExp Refl)))) r' r''
    DRTimesL e1 e1' e2 r1' -> case r'' of
      DRTimesL e1 e1'' e2 r1'' -> case uniqueDRed e1 e1' e1'' r1' r1'' of Refl -> Refl
      pat -> case pat of {}
    DRTimesR n1 e2 e2' r2' -> case r'' of
      DRTimesR n1 e2 e2'' r2'' -> case uniqueDRed e2 e2' e2'' r2' r2'' of Refl -> Refl
      pat -> case pat of {}
    pat -> case pat of {}

dredRedex :: Exp' e -> Exp' e' -> (e :-/-> e') -> Redex e
dredRedex e e' r = case r of
  DRPlus   n1 n2 _ _ -> ExpPlus (ExIntro2 (BothExp (ENat' n1,ENat' n2)) (PlusExp Refl))
  DRTimes  n1 n2 _ _ -> ExpTimes (ExIntro2 (BothExp (ENat' n1,ENat' n2)) (TimesExp Refl))
  DRPlusL  e1 _ e2 _ -> ExpPlus (ExIntro2 (BothExp (e1,e2)) (PlusExp Refl))
  DRTimesL e1 _ e2 _ -> ExpTimes (ExIntro2 (BothExp (e1,e2)) (TimesExp Refl))
  DRPlusR  n1 e2 _ _ -> ExpPlus (ExIntro2 (BothExp (ENat' n1,e2)) (PlusExp Refl))
  DRTimesR n1 e2 _ _ -> ExpTimes (ExIntro2 (BothExp (ENat' n1,e2)) (TimesExp Refl))

dredδRedex :: Exp' e -> Exp' e' -> (e :-/-> e') -> NF e' -> Redexδ e
dredδRedex e e' r ne = case ne of
  ExpNat (ExIntro n (NatExp Refl)) -> case r of
    DRPlus  n1 n2 _ _ -> ExpPlusδ  (ExIntro2 (Both (n1,n2)) (PlusExpδ Refl))
    DRTimes n1 n2 _ _ -> ExpTimesδ (ExIntro2 (Both (n1,n2)) (TimesExpδ Refl))
    pat -> case pat of {}

uniqueδDReduction :: Exp' e -> Exp' e1 -> Exp' e2 -> Redexδ e -> (e :-/-> e1) -> (e :-/-> e2) -> (e1 :=: e2)
uniqueδDReduction e e1 e2 de r1 r2 = case de of
  ExpPlusδ (ExIntro2 (Both(n1,n2)) (PlusExpδ Refl)) -> case r1 of
    DRPlus _ _ n3 p1 -> case r2 of
      DRPlus _ _ n4 p2 -> case plusUnique n1 n2 n3 n4 p1 p2 of
        Refl -> Refl
      pat -> case pat of {}
    pat -> case pat of {}
  ExpTimesδ (ExIntro2 (Both(n1,n2)) (TimesExpδ Refl)) ->  case r1 of
    DRTimes _ _ n3 t1 -> case r2 of
      DRTimes _ _ n4 t2 -> case timesUnique n1 n2 n3 n4 t1 t2 of
        Refl -> Refl
      pat -> case pat of {}
    pat -> case pat of {}

-- | 定理 2.24

detRed :: Exp' e -> Exp' e' -> (e :-/-> e') -> (e :---> e')
detRed e e' r = case r of
  DRPlus   n1 n2 n3 p  -> RPlus   n1 n2 n3 p
  DRTimes  n1 n2 n3 t  -> RTimes  n1 n2 n3 t
  DRPlusL  e1 e1' e2 r1 -> RPlusL  e1 e1' e2 (detRed e1 e1' r1)
  DRTimesL e1 e1' e2 r1 -> RTimesL e1 e1' e2 (detRed e1 e1' r1)
  DRPlusR  n1 e2 e2' r2 -> RPlusR  (ENat' n1) e2 e2' (detRed e2 e2' r2)
  DRTimesR n1 e2 e2' r2 -> RTimesR (ENat' n1) e2 e2' (detRed e2 e2' r2)

-- | 定理 2.25 (weak normalization)

newtype Normalize e n = Normalize (e :-*-> ENat n)

weakNormalization :: Exp' e -> Exists Nat' (Normalize e)
weakNormalization e = case e of
  ENat' n -> ExIntro n (Normalize (MRZero e))
  e1 :＋: e2 -> case weakNormalization e1 of
    ExIntro n1 (Normalize r1) -> case weakNormalization e2 of
      ExIntro n2 (Normalize r2) -> case plusClosure n1 n2 of
        ExIntro n3 rn3 -> ExIntro n3
                            (Normalize
                              (MRMulti e
                                       (ENat' n1 :＋: ENat' n2)
                                       (ENat' n3)
                                       (plusRLR e1 e2 n1 n2 r1 r2)
                                       (MROne (ENat' n1 :＋: ENat' n2)
                                              (ENat' n3)
                                              (RPlus n1 n2 n3 rn3))))
  e1 :×: e2 -> case weakNormalization e1 of
    ExIntro n1 (Normalize r1) -> case weakNormalization e2 of
      ExIntro n2 (Normalize r2) -> case timesClosure n1 n2 of
        ExIntro n3 rn3 -> ExIntro n3
                            (Normalize
                              (MRMulti e
                                       (ENat' n1 :×: ENat' n2)
                                       (ENat' n3)
                                       (timesRLR e1 e2 n1 n2 r1 r2)
                                       (MROne (ENat' n1 :×: ENat' n2)
                                              (ENat' n3)
                                              (RTimes n1 n2 n3 rn3))))

plusRL :: Exp' e1 -> Exp' e1' -> Exp' e2 -> (e1 :-*-> e1') -> ((e1 :＋ e2) :-*-> (e1' :＋ e2))
plusRL e1 e1' e2 r1 = case r1 of
  MRZero _        -> MRZero (e1 :＋: e2)
  MROne _ _ p     -> MROne (e1 :＋: e2) (e1' :＋: e2) (RPlusL e1 e1' e2 p)
  MRMulti _ e1'' _ p q -> MRMulti (e1 :＋: e2) (e1'' :＋: e2) (e1' :＋: e2) (plusRL e1 e1'' e2 p) (plusRL e1'' e1' e2 q)

plusRR :: Exp' e1 -> Exp' e2 -> Exp' e2' -> (e2 :-*-> e2') -> ((e1 :＋ e2) :-*-> (e1 :＋ e2'))
plusRR e1 e2 e2' r2 = case r2 of
  MRZero _        -> MRZero (e1 :＋: e2)
  MROne _ _ p     -> MROne (e1 :＋: e2) (e1 :＋: e2') (RPlusR e1 e2 e2' p)
  MRMulti _ e2'' _ p q -> MRMulti (e1 :＋: e2) (e1 :＋: e2'') (e1 :＋: e2') (plusRR e1 e2 e2'' p) (plusRR e1 e2'' e2' q)

plusRLR :: Exp' e1 -> Exp' e2 -> Nat' n1 -> Nat' n2
        -> (e1 :-*-> ENat n1) -> (e2 :-*-> ENat n2)
        -> (e1 :＋ e2) :-*-> (ENat n1 :＋ ENat n2)
plusRLR e1 e2 n1 n2 r1 r2 = MRMulti (e1 :＋: e2) (ENat' n1 :＋: e2) (ENat' n1 :＋: ENat' n2)
                                    (plusRL e1 (ENat' n1) e2 r1) (plusRR (ENat' n1) e2 (ENat' n2) r2)
                            
timesRL :: Exp' e1 -> Exp' e1' -> Exp' e2 -> (e1 :-*-> e1') -> ((e1 :× e2) :-*-> (e1' :× e2))
timesRL e1 e1' e2 r1 = case r1 of
  MRZero _        -> MRZero (e1 :×: e2)
  MROne _ _ p     -> MROne (e1 :×: e2) (e1' :×: e2) (RTimesL e1 e1' e2 p)
  MRMulti _ e1'' _ p q -> MRMulti (e1 :×: e2) (e1'' :×: e2) (e1' :×: e2) (timesRL e1 e1'' e2 p) (timesRL e1'' e1' e2 q)

timesRR :: Exp' e1 -> Exp' e2 -> Exp' e2' -> (e2 :-*-> e2') -> ((e1 :× e2) :-*-> (e1 :× e2'))
timesRR e1 e2 e2' r2 = case r2 of
  MRZero _        -> MRZero (e1 :×: e2)
  MROne _ _ p     -> MROne (e1 :×: e2) (e1 :×: e2') (RTimesR e1 e2 e2' p)
  MRMulti _ e2'' _ p q -> MRMulti (e1 :×: e2) (e1 :×: e2'') (e1 :×: e2') (timesRR e1 e2 e2'' p) (timesRR e1 e2'' e2' q)

timesRLR :: Exp' e1 -> Exp' e2 -> Nat' n1 -> Nat' n2
         -> (e1 :-*-> ENat n1) -> (e2 :-*-> ENat n2)
         -> (e1 :× e2) :-*-> (ENat n1 :× ENat n2)
timesRLR e1 e2 n1 n2 r1 r2 = MRMulti (e1 :×: e2) (ENat' n1 :×: e2) (ENat' n1 :×: ENat' n2)
                                     (timesRL e1 (ENat' n1) e2 r1) (timesRR (ENat' n1) e2 (ENat' n2) r2)
                            
-- | 定理 2.26 (strong normalization)

data Absurd
type Not a = a -> Absurd

notProgressive :: Exp' e -> NF e -> Not (Exists Exp' ((:--->) e))
notProgressive _ nf = case nf of {}

reduceSize :: Exp' e -> Exp' e' -> (e :---> e') -> (Size e :=: S (Size e'))
reduceSize e e' r = case r of
  RPlus _ _ _ _       -> Refl
  RTimes _ _ _ _      -> Refl
  RPlusL e1 e1' e2 r1  -> case reduceSize e1 e1' r1 of Refl -> Refl
  RTimesL e1 e1' e2 r1 -> case reduceSize e1 e1' r1 of Refl -> Refl
  RPlusR e1 e2 e2' r2  -> case reduceSize e2 e2' r2 of
    Refl -> case (size e, size e') of
      (n,n') -> case (size e1, size e2, size e2') of
         (n1,n2,n2') -> case plusClosure n1 n2 of
           ExIntro n3 p -> case addUnique n1 n2 n3 p of
             Refl -> case plusClosure n1 n2' of
               ExIntro n3' p' -> case addUnique n1 n2' n3' p' of
                 Refl -> case addUnique n1 (S' n2') (S' n3') (plusSucc n1 n2' n3' p') of
                   Refl -> Refl
  RTimesR e1 e2 e2' r2 -> case reduceSize e2 e2' r2 of
    Refl -> case (size e, size e') of
      (n,n') -> case (size e1, size e2, size e2') of
         (n1,n2,n2') -> case plusClosure n1 n2 of
           ExIntro n3 p -> case addUnique n1 n2 n3 p of
             Refl -> case plusClosure n1 n2' of
               ExIntro n3' p' -> case addUnique n1 n2' n3' p' of
                 Refl -> case addUnique n1 (S' n2') (S' n3') (plusSucc n1 n2' n3' p') of
                   Refl -> Refl

newtype RdInvariant e e' n = RdInvariant (Size e :=: (n :+ Size e'))

rdseq :: Exp' e -> Exp' e' -> Exp' e'' -> (e :-*-> e') -> (e' :---> e'') -> Exists Nat' (RdInvariant e e'')
rdseq e ei ei' mr sr' = case normalize mr of
  MRZero _             -> case reduceSize ei ei' sr' of
    Refl -> ExIntro (S' Z') (RdInvariant Refl)
  MROne _ _ sr          -> case rdseq e e ei (MRZero e) sr of
    ExIntro _ (RdInvariant Refl) -> case reduceSize e ei sr of
      Refl -> case reduceSize ei ei' sr' of
        Refl -> ExIntro (S' (S' Z')) (RdInvariant Refl)
  MRMulti _ e' _ r' ri -> case ri of
    MROne _ _ r1 -> case rdseq e e' ei r' r1 of
      ExIntro n (RdInvariant Refl) -> case reduceSize ei ei' sr' of
        Refl -> case uniqSucc n (size ei') of
          Refl -> ExIntro (S' n) (RdInvariant Refl)
    pat -> case pat of {}

newtype InRdSeq (e0 :: Exp) (e :: Exp) (i :: Nat) = InRdSeq (e0 :-*-> e, RdInvariant e0 e i)

propSize :: Exp' e -> Not (Size e :=: Z)
propSize e = case e of {}

introZero :: Nat' m -> Nat' n -> m :=: (m :+ n) -> n :=: Z
introZero m n Refl = case addUnique' m n m Refl of
  PZero _ -> Refl
  PSucc m' _ _ p -> case introZero m' n (addUnique m' n m' p) of Refl -> Refl
  
