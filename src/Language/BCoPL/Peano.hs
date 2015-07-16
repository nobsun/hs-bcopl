{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.BCoPL.Peano where

data Nat = Z 
         | S Nat deriving (Eq,Ord,Read)

instance Show Nat where
  show Z = "Z"
  show (S n) = "S("++show n++")"

data Nat' n where
  Z'   :: Nat' Z
  S'   :: Nat' n -> Nat' (S n)

instance Show (Nat' Z) where
  show Z' = "Z"

instance Show (Nat' n) => Show (Nat' (S n)) where
  show (S' n) = "S("++show n++")"




