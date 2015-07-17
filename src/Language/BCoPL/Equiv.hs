{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Language.BCoPL.Equiv where

data a :=: b where
  Refl  :: a :=: a
  Sym   :: a :=: b -> b :=: a
  Trans :: a :=: b -> b :=: c -> a :=: c


