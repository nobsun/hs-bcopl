module Language.BCoPL.DataLevel.ML1 (
    -- * Types
    Val(..)
  , Exp(..)
    -- * Utilities
  , operator
  , loperand
  , roperand
  ) where

import Data.Char (isDigit,isAlpha,isSpace,toLower)
import Text.ParserCombinators.ReadP

data Val = Int Int
         | Bool Bool
         deriving (Eq)

isInt :: Val -> Bool
isInt (Int _) = True
isInt _       = False

instance Show Val where
  show (Int n)  = show n
  show (Bool b) = map toLower (show b)

instance Read Val where
  readsPrec _ "false" = [(Bool False,"")]
  readsPrec _ "true"  = [(Bool True,"")]
  readsPrec _ s       = case span isDigit s' of
    ("",_)  -> case span isAlpha s' of
      (bs,cs) | map toLower bs == "false" -> [(Bool False,cs)]
              | map toLower bs == "true"  -> [(Bool True,cs)]
    (is,cs) -> [(Int (read is),cs)]
    where s' = dropWhile isSpace s

data Exp = Val Val
         | Exp :+: Exp
         | Exp :-: Exp
         | Exp :*: Exp
         | Exp :<: Exp
         | IF Exp Exp Exp
         deriving (Eq)

operator :: Exp -> (Exp -> Exp -> Exp)
operator (_ :+: _) = (:+:)
operator (_ :*: _) = (:*:)
operator (_ :-: _) = (:-:)
operator (_ :<: _) = (:<:)

loperand :: Exp -> Exp
loperand (l :+: _) = l
loperand (l :*: _) = l
loperand (l :-: _) = l
loperand (l :<: _) = l

roperand :: Exp -> Exp
roperand (_ :+: r) = r
roperand (_ :*: r) = r
roperand (_ :-: r) = r
roperand (_ :<: r) = r

instance Show Exp where
  show e = case e of
    Val v     -> show v
    e1 :+: e2 -> show e1 ++ " + " ++ show e2
    e1 :-: e2 -> show e1 ++ " + " ++ show e2
    e1 :*: e2 -> show' e1 ++ " * " ++ show' e2
    e1 :<: e2 -> show e1 ++ " * " ++ show e2
    IF e1 e2 e3 -> "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
    where
      show' e' = case e' of
        e1' :+: e2' -> "("++show e'++")"
        _           -> show e'

instance Read Exp where
  readsPrec _ = readP_to_S expr

expr :: ReadP Exp
expr = term `chainl1` addop
term = factor `chainl1` mulop

mulop = do { skipSpaces
           ; string "*"
           ; skipSpaces
           ; return (:*:)
           }

addop = do { skipSpaces
           ; string "+"
           ; skipSpaces
           ; return (:+:)
           }

factor :: ReadP Exp
factor = parens expr +++ val

val :: ReadP Exp
val = readS_to_P reads >>= return . Val

bool :: ReadP Bool
bool = do { skipSpaces
          ; s <- many1 (satisfy isAlpha)
          ; skipSpaces
          ; return (read s)
          }

parens :: ReadP a -> ReadP a
parens p =  do { skipSpaces 
               ; char '('
               ; skipSpaces
               ; c <- p
               ; skipSpaces
               ; char ')'
               ; return c
               }
