module Main where

import Test.DocTest

main :: IO ()
main = doctest ["src/Language/BCoPL/MetaTheory/Nat.hs"]

