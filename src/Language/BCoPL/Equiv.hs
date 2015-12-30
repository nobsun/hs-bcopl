{-# LANGUAGE NPlusKPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}

module Language.BCoPL.Equiv where

data a :=: b where
  Refl  :: a :=: a
  
deriving instance Show (a :=: b)

eqSym :: a :=: b -> b :=: a
eqSym Refl = Refl

eqTrans :: a :=: b -> b :=: c -> a :=: c
eqTrans Refl Refl = Refl

eqCong  :: a :=: b -> f a :=: f b
eqCong Refl = Refl
