module Main where

import Test.DocTest

main :: IO ()
main = doctest ["src/Language/BCoPL/TypeLevel/MetaTheory/Nat.hs"]

