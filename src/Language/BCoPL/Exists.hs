{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.BCoPL.Exists where

data Exists (s :: k -> *) (p :: k -> *) where
  ExIntro :: s a -> p a -> Exists s p
