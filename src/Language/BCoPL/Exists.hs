{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.BCoPL.Exists where

data Exists (s :: k -> *) (p :: k -> *) where
  ExIntro :: s a -> p a -> Exists s p

data Exists2 (s :: j -> k -> *) (p :: j -> k -> *) where
  ExIntro2 :: s a b -> p a b -> Exists2 s p
