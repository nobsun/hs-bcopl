module Language.BCoPL.Derivation (
    -- * Types
    Tree (..)
  , Derivation
  , Deducer
    -- * Display derivation
  , derivation
  ) where

import Data.Tree (Tree (..))
import Language.BCoPL.Diagram (Diagram(..),renderDiagram,ppr,textDiag)

type Derivation a = Tree (String,a)
type Deducer a = a -> [Derivation a]

derivation :: (Show a) => Deducer a -> (a -> String)
derivation deducer = renderDiagram . deduction deducer

deduction :: (Show a) => Deducer a -> (a -> Diagram)
deduction deducer j = case deducer j of
  t:_ -> ppr t
  []  -> textDiag $ show j ++ ": Cannot be deduced"

