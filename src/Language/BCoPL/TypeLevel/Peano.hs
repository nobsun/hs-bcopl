{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.BCoPL.TypeLevel.Peano where

import Data.Char
import Data.List

data Nat = Z 
         | S Nat deriving (Eq,Ord,Show,Read)

data Nat' (n :: Nat) where
  Z'    :: Nat' Z
  S'    :: Nat' n -> Nat' (S n)

instance Show (Nat' n) where
  show Z'     = "Z"
  show (S' n) = "S("++show n++")"

instance Read (Nat' Z) where
  readsPrec _ s = case trim s of
    "Z" -> [(Z',"")]
    _   -> []

instance Read (Nat' n) => Read (Nat' (S n)) where
  readsPrec _ s = case trim s of
        'S':'(':rs -> [(S'(read (init rs)),"")]
        _          -> []
       
trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

type family (m :: Nat) :+ (n :: Nat) :: Nat
type instance Z :+ n = n
type instance (S m) :+ n = S (m :+ n)

type family (m :: Nat) :* (n :: Nat) :: Nat
type instance     Z :* n = Z
type instance (S m) :* n = n :+ (m :* n)

add :: Nat' n1 -> Nat' n2 -> Nat' (n1 :+ n2)
add n1 n2 = case n1 of
  Z'     -> n2
  S' n1' -> S' (add n1' n2)

mul :: Nat' n1 -> Nat' n2 -> Nat' (n1 :* n2)
mul n1 n2 = case n1 of
  Z'     -> Z'
  S' n1' -> add n2 (mul n1' n2)
