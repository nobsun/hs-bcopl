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
module Language.BCoPL.Equiv where

data a :=: b where
  Refl  :: a :=: a
  Sym   :: a :=: b -> b :=: a
  Trans :: a :=: b -> b :=: c -> a :=: c
  Cong  :: a :=: b -> f a :=: f b
