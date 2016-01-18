{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE PolyKinds #-}
module Language.BCoPL.TypeLevel.Not where

data Absurd

type Not a = a -> Absurd
