{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.BCoPL.Exp where

import Language.BCoPL.Peano

data Exp = Nat Nat
         | Add Exp Exp
         | Mul Exp Exp

data Exp' (e :: Exp) where
  Nat' :: Exp' (Nat Nat)
  Add' :: Exp' e1 -> Exp' e2 -> Exp' (Add e1 e2)
  Mul' :: Exp' e1 -> Exp' e2 -> Exp' (Mul e1 e2)

