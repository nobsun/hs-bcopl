{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module Language.BCoPL.TypeLevel.Exists where

data Exists (s :: k -> *) (p :: k -> *) where
  ExIntro :: s a -> p a -> Exists s p

data Exists2 (s :: j -> k -> *) (p :: j -> k -> *) where
  ExIntro2 :: s a b -> p a b -> Exists2 s p
