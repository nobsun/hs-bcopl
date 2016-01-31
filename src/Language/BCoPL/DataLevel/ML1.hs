{-# LANGUAGE EmptyCase #-}
module Language.BCoPL.DataLevel.ML1 (
    -- * Types
    Val(..)
  , Exp(..)
    -- * Utilities
  -- , operator
  -- , loperand
  -- , roperand
  ) where

import Data.Char (isDigit,toLower,digitToInt)
import Text.ParserCombinators.ReadP

data Val = Int Int
         | Bool Bool
         deriving (Eq)

instance Show Val where
  show (Int n)  = show n
  show (Bool b) = map toLower (show b)

instance Read Val where
  readsPrec _ = readP_to_S pVal

pVal :: ReadP Val
pVal = skipSpaces >> (pInt +++ pBool)

pInt = pNegInt +++ pPosInt

pNegInt = char '-' >> pPosInt >>= \ (Int n) -> return (Int (negate n))
pPosInt = many1 (satisfy isDigit) >>= return . Int . foldl ((+) . (10 *)) 0 . map digitToInt 

pBool = pFalse +++ pTrue
pFalse = string "false" >> return (Bool False)
pTrue  = string "true"  >> return (Bool True)

data Exp = Val Val
         | Exp :+: Exp
         | Exp :-: Exp
         | Exp :*: Exp
         | Exp :<: Exp
         | IF Exp Exp Exp
         deriving (Eq)

{- -
instance Show Exp where
  show e = case e of
    Val v     -> show v
    e1 :+: e2 -> show e1 ++ " + " ++ show e2
    e1 :-: e2 -> show e1 ++ " - " ++ show e2
    e1 :*: e2 -> show' e1 ++ " * " ++ show' e2
    e1 :<: e2 -> show e1 ++ " < " ++ show e2
    IF e1 e2 e3 -> "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
    where
      show' e' = case e' of
        e1' :+: e2' -> "("++show e'++")"
        e1' :-: e2' -> "("++show e'++")"
        _           -> show e'
-- -}

{- -}
instance Show Exp where
  show e = case e of
    Val v     -> show v
    e1 :+: e2 -> "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
    e1 :-: e2 -> "(" ++ show e1 ++ " - " ++ show e2 ++ ")"
    e1 :*: e2 -> "(" ++ show e1 ++ " * " ++ show e2 ++ ")"
    e1 :<: e2 -> "(" ++ show e1 ++ " < " ++ show e2 ++ ")"
    IF e1 e2 e3 -> "(" ++ "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3 ++")"
-- -}

instance Read Exp where
  readsPrec _ = readP_to_S expr1

expr1 :: ReadP Exp
expr1 = ifexpr +++ binop +++ expr2
expr2 :: ReadP Exp
expr2 = chainl1 expr3 cmpop
expr3 :: ReadP Exp
expr3 = chainl1 expr4 addop
expr4 :: ReadP Exp
expr4 = chainl1 aexpr mulop
aexpr :: ReadP Exp
aexpr = val +++ parens expr1

ifexpr :: ReadP Exp
ifexpr = do
  { skipSpaces
  ; string "if"
  ; skipSpaces
  ; e1 <- expr1
  ; skipSpaces
  ; string "then"
  ; skipSpaces
  ; e2 <- expr1
  ; skipSpaces
  ; string "else"
  ; skipSpaces
  ; e3 <- expr1
  ; return $ IF e1 e2 e3
  }

binop :: ReadP Exp
binop = cmpexp +++ addexp +++ mulexp

cmpexp :: ReadP Exp
cmpexp = do { skipSpaces
            ; e1 <- expr3
            ; op <- cmpop
            ; e2 <- ifexpr
            ; skipSpaces
            ; return (op e1 e2)
            }

addexp :: ReadP Exp
addexp = do { skipSpaces
            ; e1 <- expr4
            ; op <- addop
            ; e2 <- ifexpr
            ; skipSpaces
            ; return (op e1 e2)
            }

mulexp :: ReadP Exp
mulexp = do { skipSpaces
            ; e1 <- aexpr
            ; op <- mulop
            ; e2 <- ifexpr
            ; skipSpaces
            ; return (op e1 e2)
            }

cmpop :: ReadP (Exp -> Exp -> Exp)
cmpop = do { skipSpaces
           ; string "<"
           ; skipSpaces
           ; return (:<:)
           }

addop :: ReadP (Exp -> Exp -> Exp)
addop = do { skipSpaces
           ; op <- string "+" +++ string "-"
           ; skipSpaces
           ; return (if op == "+" then (:+:) else (:-:))
           }

mulop :: ReadP (Exp -> Exp -> Exp)
mulop = do { skipSpaces
           ; string "*"
           ; skipSpaces
           ; return (:*:)
           }

val :: ReadP Exp
val = pVal >>= return . Val

parens :: ReadP a -> ReadP a
parens = between (char '(') (char ')')
