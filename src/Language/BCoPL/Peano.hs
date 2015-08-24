{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Language.BCoPL.Peano where

import Data.Char
import Data.List
import Text.ParserCombinators.ReadP

data Nat = Z 
         | S Nat deriving (Eq,Ord,Show,Read)

type family (m :: Nat) :+ (n :: Nat) :: Nat
type instance Z :+ n = n
type instance (S m) :+ n = S (m :+ n)

type family (m :: Nat) :* (n :: Nat) :: Nat
type instance     Z :* n = Z
type instance (S m) :* n = (m :* n) :+ n 

data Nat' (n :: Nat) where
  Z'    :: Nat' Z
  S'    :: Nat' n -> Nat' (S n)
  (:+:) :: Nat' m -> Nat' n -> Nat' (m :+ n)
  (:*:) :: Nat' m -> Nat' n -> Nat' (m :* n)

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
