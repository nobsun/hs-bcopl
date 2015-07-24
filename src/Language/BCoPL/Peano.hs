{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.BCoPL.Peano where

import Data.Char
import Data.List
import Text.ParserCombinators.ReadP

data Nat = Z 
         | S Nat deriving (Eq,Ord,Read)

instance Show Nat where
  show Z     = "Z"
  show (S n) = "S("++show n++")"

data Nat' n where
  Z'   :: Nat' Z
  S'   :: Nat' n -> Nat' (S n)

instance Show (Nat' n) where
  show Z'     = "Z"
  show (S' n) = "S("++show n++")"

instance Read (Nat' Z) where
  readsPrec _ s = case trim s of "Z" -> [(Z',"")]

instance Read (Nat' n) => Read (Nat' (S n)) where
  readsPrec _ s = case trim s of
    'S':'(':rs -> [(S' (read (init rs)),"")]
    'S':rs     -> [(S' (read rs),"")]
    _          -> []

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace
