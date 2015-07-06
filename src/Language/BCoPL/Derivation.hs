{-# LANGUAGE ScopedTypeVariables #-}
module Language.BCoPL.Derivation (
    -- * Types
    Tree (..)
  , Deducer
  , Derivation
    -- * Session generator for deriving judgement
  , sessionGen
  ) where

import Control.Exception (catch, SomeException)
import Data.Char (toLower)
import Data.List (isPrefixOf)
import Data.Tree (Tree (..))
import Language.BCoPL.Diagram (Diagram(..),renderDiagram,ppr,textDiag)

type Derivation a = Tree (String,a)
type Deducer a = a -> [Derivation a]

sessionGen :: (Read a, Show a) => (String, Deducer a) -> IO ()
sessionGen (p,d) = prompt p ":q" (derivation d)

prompt :: (Read a) => String -> String -> (a -> String) -> IO ()
prompt p q d = do 
  { putStr p
  ; input <- getLine
  ; if q `isPrefixOf` map toLower input then return ()
    else do { catch
                (putStrLn $ d (read input))
                (\ (e::SomeException) -> putStrLn (show e))
            ; prompt p q d
            }
  }

derivation :: (Show a) => Deducer a -> (a -> String)
derivation deducer = renderDiagram . deduction deducer

deduction :: (Show a) => Deducer a -> (a -> Diagram)
deduction deducer j = case deducer j of
  t:_ -> ppr t
  []  -> textDiag $ show j ++ ": Cannot be deduced"

instance Show Diagram where
  show = renderDiagram

