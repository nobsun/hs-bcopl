{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE EmptyCase #-}
module Language.BCoPL.TypeLevel.MetaTheory.Semantics where

import Language.BCoPL.TypeLevel.Peano
import Language.BCoPL.TypeLevel.Exp
import Language.BCoPL.TypeLevel.EvalNatExp
import Language.BCoPL.TypeLevel.ReduceNatExp
-- import Language.BCoPL.TypeLevel.MetaTheory.EvalNatExp
-- import Language.BCoPL.TypeLevel.MetaTheory.ReduceNatExp

-- | 定理 2.27

evalReduce :: Exp' e -> Nat' n -> EvalTo e n -> e :-*-> ENat n
evalReduce e n ev = case ev of
  EConst _ -> MRZero e
  EPlus e1 e2 n1 n2 _n ev1 ev2 p -> case evalReduce e1 n1 ev1 of
    rd1 -> case evalReduce e2 n2 ev2 of
      rd2 -> case plusSubRedL e1 (ENat' n1) e2 rd1 of
        rd -> case plusSubRedR (ENat' n1) e2 (ENat' n2) rd2 of
          rd' -> MRMulti (e1 :＋: e2) (ENat' n1 :＋: ENat' n2) (ENat' n)
                   (MRMulti (e1 :＋: e2) (ENat' n1 :＋: e2) (ENat' n1 :＋: ENat' n2) rd rd')
                   (MROne (ENat' n1 :＋: ENat' n2) (ENat' n) (RPlus n1 n2 n p))
  ETimes e1 e2 n1 n2 _n ev1 ev2 p -> case evalReduce e1 n1 ev1 of
    rd1 -> case evalReduce e2 n2 ev2 of
      rd2 -> case timesSubRedL e1 (ENat' n1) e2 rd1 of
        rd -> case timesSubRedR (ENat' n1) e2 (ENat' n2) rd2 of
          rd' -> MRMulti (e1 :×: e2) (ENat' n1 :×: ENat' n2) (ENat' n)
                   (MRMulti (e1 :×: e2) (ENat' n1 :×: e2) (ENat' n1 :×: ENat' n2) rd rd')
                   (MROne (ENat' n1 :×: ENat' n2) (ENat' n) (RTimes n1 n2 n p))

plusSubRedL :: Exp' e1 -> Exp' e1' -> Exp' e2 -> e1 :-*-> e1' -> (e1 :＋ e2) :-*-> (e1' :＋ e2)
plusSubRedL e1 e1' e2 mr1 = case mr1 of
  MRZero _     -> MRZero (e1 :＋: e2)
  MROne _ _ r1 -> MROne (e1 :＋: e2) (e1' :＋: e2) (RPlusL e1 e1' e2 r1)
  MRMulti _ e1'' _ mr1'' mr1' -> MRMulti (e1 :＋: e2) (e1'' :＋: e2) (e1' :＋: e2)
                                         (plusSubRedL e1 e1'' e2 mr1'') (plusSubRedL e1'' e1' e2 mr1')

plusSubRedR :: Exp' e1 -> Exp' e2 -> Exp' e2' -> e2 :-*-> e2' -> (e1 :＋ e2) :-*-> (e1 :＋ e2')
plusSubRedR e1 e2 e2' mr2 = case mr2 of
  MRZero _     -> MRZero (e1 :＋: e2)
  MROne _ _ r2 -> MROne (e1 :＋: e2) (e1 :＋: e2') (RPlusR e1 e2 e2' r2)
  MRMulti _ e2'' _ mr2'' mr2' -> MRMulti (e1 :＋: e2) (e1 :＋: e2'') (e1 :＋: e2')
                                         (plusSubRedR e1 e2 e2'' mr2'') (plusSubRedR e1 e2'' e2' mr2')

timesSubRedL :: Exp' e1 -> Exp' e1' -> Exp' e2 -> e1 :-*-> e1' -> (e1 :× e2) :-*-> (e1' :× e2)
timesSubRedL e1 e1' e2 mr1 = case mr1 of
  MRZero _     -> MRZero (e1 :×: e2)
  MROne _ _ r1 -> MROne (e1 :×: e2) (e1' :×: e2) (RTimesL e1 e1' e2 r1)
  MRMulti _ e1'' _ mr1'' mr1' -> MRMulti (e1 :×: e2) (e1'' :×: e2) (e1' :×: e2)
                                         (timesSubRedL e1 e1'' e2 mr1'') (timesSubRedL e1'' e1' e2 mr1')

timesSubRedR :: Exp' e1 -> Exp' e2 -> Exp' e2' -> e2 :-*-> e2' -> (e1 :× e2) :-*-> (e1 :× e2')
timesSubRedR e1 e2 e2' mr2 = case mr2 of
  MRZero _     -> MRZero (e1 :×: e2)
  MROne _ _ r2 -> MROne (e1 :×: e2) (e1 :×: e2') (RTimesR e1 e2 e2' r2)
  MRMulti _ e2'' _ mr2'' mr2' -> MRMulti (e1 :×: e2) (e1 :×: e2'') (e1 :×: e2')
                                         (timesSubRedR e1 e2 e2'' mr2'') (timesSubRedR e1 e2'' e2' mr2')

-- | 定理 2.28

reduceEval :: Exp' e -> Nat' n -> e :-*-> ENat n -> EvalTo e n
reduceEval e n rd = case normalizeMRM rd of
  MRZero _     -> EConst n
  MROne e' _ r -> case r of
    RPlus n1 n2 _ p  -> EPlus (ENat' n1) (ENat' n2) n1 n2 n (EConst n1) (EConst n2) p
    RTimes n1 n2 _ t -> ETimes (ENat' n1) (ENat' n2) n1 n2 n (EConst n1) (EConst n2) t
    pat -> case pat of {}
  MRMulti _ drdx _ mr mr' -> undefined
