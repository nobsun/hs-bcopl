{-# LANGUAGE NPlusKPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Language.BCoPL.Nat (
    -- * Types
      Nat(..)
    , Judge(..)
    , Derivation
    -- * Derivation
    , deduce
    , derivation
    ) where

import Data.Tree (Tree(..))
import Text.PrettyPrint.Boxes

data Nat = Z 
         | S Nat
         deriving (Eq,Ord)

instance Show Nat where
  show Z     = "Z"
  show (S n) = "S("++show n++")"

instance Enum Nat where
  succ n = S n
  pred (S n) = n
  toEnum 0     = Z
  toEnum (n+1) = S (toEnum n)
  fromEnum Z     = 0
  fromEnum (S n) = succ (fromEnum n)

data Judge = Plus { k,m,n :: Nat }
           | Times { k,m,n :: Nat }
           deriving (Eq)

instance Show Judge where
  show (Plus k m n)  = show k ++ " plus " ++ show m ++ " is " ++ show n
  show (Times k m n) = show k ++ " times " ++ show m ++ " is " ++ show n

type Derivation = Tree (String,Judge)

instance Show Derivation where
  show = render . diagram . ppr

deduce :: Judge -> [Derivation]
deduce j = case j of
  Plus Z n1 n2 | n1 == n2 -> [Node ("P-Zero",j) []]
  Plus (S n1) n2 (S n3)   -> deduce (Plus n1 n2 n3) >>= \ j' ->
                             [Node ("P-Succ",j) [j']]
  Times Z _ n  | n == Z   -> return (Node ("T-Zero",j) [])
  Times (S n1) n2 n4      -> [Z .. n4] >>= \ n3 ->
                             deduce (Plus n2 n3 n4)  >>= \ j2 ->
                             deduce (Times n1 n2 n3) >>= \ j1 ->
                             [Node ("T-Succ",j) [j1,j2]]
  _                       -> []

data Diagram = Diagram {leading,judgement,trailing :: Int, diagram :: Box}

derivation :: Judge -> String
derivation = render . diagram . deduction

deduction :: Judge -> Diagram
deduction j = case deduce j of
  t:_ -> ppr t
  []  -> err
    where
      err = Diagram { leading = 0, judgement = length msg, trailing = 0
                    , diagram = text $ msg
                    }
      msg = show j ++ ": Cannot deduced"

ppr :: Derivation -> Diagram
ppr (Node (rn,j) ts) = case pprs ts of
  Diagram tlead tjudge ttrail tdia
    -> Diagram dlead djudge dtrail ddia
       where
         (blead,bjudge,btrail,bdia) = (0,cols bdia,0,text (show j))
         bdia'  = moveRight blead' bdia
         (tlead',blead') = if tent > bent then (tlead,blead+(tent-bent)`div`2)
                           else (tlead+(bent-tent)`div`2,blead)
         (tent,bent) = (2*tlead+tjudge,2*blead+bjudge)
         tdia'  = moveRight (tlead' - tlead) tdia
         mlead' = tlead' `min` blead'
         mdia   = text $ replicate (tjudge `max` bjudge) '-' ++ "(" ++ rn ++ ")"
         mdia'  = moveRight (tlead' `min` blead') mdia
         ddia   = tdia' // mdia' // bdia'
         dlead  = blead'
         djudge = cols bdia
         dtrail = cols ddia - dlead - djudge

pprs :: [Derivation] -> Diagram
pprs [] = Diagram 0 0 0 (text "")
pprs ts = Diagram dlead djudge dtrail ddia
  where
    bs  = map ppr ts
    dlead  = leading $ head bs
    djudge = cols ddia - dlead - dtrail
    dtrail = trailing $ last bs
    ddia   = hsep 3 bottom $ map diagram bs
