{-# LANGUAGE TemplateHaskell #-}
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
module Language.BCoPL.CompareNat (
  ) where

import Language.BCoPL.Peano

data LessThan1 (n1 :: Nat) (n2 :: Nat) where
  LSucc1  :: Nat' n -> LessThan1 n (S n)
  LTrans1 :: Nat' n1 -> Nat' n2 -> Nat' n3 -> LessThan1 n1 n3
  
data LessThan2 (n1 :: Nat) (n2 :: Nat) where
  LZero2 :: Nat' n -> LessThan2 Z (S n)
  LSuccSucc2 :: Nat' n1 -> Nat' n2 -> LessThan2 n1 n2 -> LessThan2 (S n1) (S n2)

data LessThan3 (n1 :: Nat) (n2 :: Nat) where
  LSucc3 ::  Nat' n -> LessThan3 n (S n)
  LSuccR3 :: Nat' n1 -> Nat' n2 -> LessThan3 n1 n2 -> LessThan3 n1 (S n2)
