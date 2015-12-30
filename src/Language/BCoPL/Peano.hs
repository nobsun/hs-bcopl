{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.BCoPL.Peano where

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
