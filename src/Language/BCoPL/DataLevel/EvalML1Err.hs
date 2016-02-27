module Language.BCoPL.DataLevel.EvalML1Err where

-- import Debug.Trace
import Data.Char (toLower)
import Language.BCoPL.DataLevel.ML1
import Language.BCoPL.DataLevel.Derivation (Tree(..),Deducer,sessionGen,sessionGen')

data Judge = EvalTo Exp (Maybe Val)
           | Plus  {k,m,n :: Int}
           | Minus {k,m,n :: Int}
           | Times {k,m,n :: Int}
           | LessThan {p,q :: Int, r :: Bool}

instance Show Judge where
  show (EvalTo e (Just v)) = unwords [show e,"evalto",show v]
  show (EvalTo e Nothing)  = unwords [show e,"evalto","error"]
  show (Plus k m n)  = unwords [show k,"plus", show m,"is",show n]
  show (Minus k m n) = unwords [show k,"minus",show m,"is",show n]
  show (Times k m n) = unwords [show k,"times",show m,"is",show n]
  show (LessThan p q r) = unwords [show p,"less than",show q,"is",map toLower (show r)]

instance Read Judge where
  readsPrec _ s = case words s of
    ws -> case break ("evalto"==) ws of
     (xs,_:ys) -> if ys == ["error"] then [(EvalTo (read (concat xs)) Nothing,"")]
                  else [(EvalTo (read (concat xs)) (Just (read (concat ys))),"")]
     _         -> case break ("plus"==) ws of
       ([k],_:m:"is":[n]) -> [(Plus (read k) (read m) (read n),"")]
       _                  -> case break ("minus"==) ws of
         ([k],_:m:"is":[n]) -> [(Minus (read k) (read m) (read n),"")]
         _                  -> case break ("times"==) ws of
           ([k],_:m:"is":[n]) -> [(Times (read k) (read m) (read n),"")]
           _                  -> case break ("less"==) ws of
             ([p],_:_:q:"is":[r]) -> [(LessThan (read p) (read q) (read r),"")]
             _ -> error ("Syntax error!: " ++ s)

deduce :: Deducer Judge
deduce j = case j of
  EvalTo e Nothing  -> case e of
    IF e1 e2 e3 -> take 1
                   $
                   [ Node ("E-IfError",j) [err] | err <- deduce (EvalTo e1 Nothing) ]
                   ++
                   [ Node ("E-IfTError",j) [k,err]
                   | k   <- deduce (EvalTo e1 (Just (Bool True)))
                   , err <- deduce (EvalTo e2 Nothing)
                   ]
                   ++
                   [ Node ("E-IfFError",j) [k,err]
                   | k   <- deduce (EvalTo e1 (Just (Bool False)))
                   , err <- deduce (EvalTo e3 Nothing)
                   ]
                   ++ 
                   [ Node ("E-IfInt",j) [k]
                   | i <- ints maxBound
                   , k <- deduce (EvalTo e1 (Just (Int i)))
                   ]
    e1 :+: e2   -> take 1
                   $
                   [ Node ("E-PlusBoolL",j) [k]
                   | b <- [False,True]
                   , k <- deduce (EvalTo e1 (Just (Bool b)))
                   ]
                   ++
                   [ Node ("E-PlusBoolR",j) [k]
                   | b <- [False,True]
                   , k <- deduce (EvalTo e2 (Just (Bool b)))
                   ]
                   ++
                   [ Node ("E-PlusErrorL",j) [err] | err <- deduce (EvalTo e1 Nothing) ]
                   ++
                   [ Node ("E-PlusErrorR",j) [err] | err <- deduce (EvalTo e2 Nothing) ]
    e1 :-: e2   -> take 1
                   $
                   [ Node ("E-MinusBoolL",j) [k]
                   | b <- [False,True]
                   , k <- deduce (EvalTo e1 (Just (Bool b)))
                   ]
                   ++
                   [ Node ("E-MinusBoolR",j) [k]
                   | b <- [False,True]
                   , k <- deduce (EvalTo e2 (Just (Bool b)))
                   ]
                   ++
                   [ Node ("E-MinusErrorL",j) [err] | err <- deduce (EvalTo e1 Nothing) ]
                   ++
                   [ Node ("E-MinusErrorR",j) [err] | err <- deduce (EvalTo e2 Nothing) ]
    e1 :*: e2   -> take 1
                   $
                   [ Node ("E-TimesBoolL",j) [k]
                   | b <- [False,True]
                   , k <- deduce (EvalTo e1 (Just (Bool b)))
                   ]
                   ++
                   [ Node ("E-TimesBoolR",j) [k]
                   | b <- [False,True]
                   , k <- deduce (EvalTo e2 (Just (Bool b)))
                   ]
                   ++
                   [ Node ("E-TimesErrorL",j) [err] | err <- deduce (EvalTo e1 Nothing) ]
                   ++
                   [ Node ("E-TimesErrorR",j) [err] | err <- deduce (EvalTo e2 Nothing) ]
    e1 :<: e2   -> take 1
                   $
                   [ Node ("E-LtBoolL",j) [k]
                   | b <- [False,True]
                   , k <- deduce (EvalTo e1 (Just (Bool b)))
                   ]
                   ++
                   [ Node ("E-LtBoolR",j) [k]
                   | b <- [False,True]
                   , k <- deduce (EvalTo e2 (Just (Bool b)))
                   ]
                   ++
                   [ Node ("E-LtErrorL",j) [err] | err <- deduce (EvalTo e1 Nothing) ]
                   ++
                   [ Node ("E-LtErrorR",j) [err] | err <- deduce (EvalTo e2 Nothing) ]
    Val _ -> []
  EvalTo e (Just v) -> case v of
    Int n  -> case e of
      Val (Int n') 
        | n' == n -> [Node ("E-Int",j) []]
        | True    -> []
      IF e1 e2 e3 -> take 1
                     $ 
                     [ Node ("E-IfT",j) [j1,j2]
                     | j1 <- deduce (EvalTo e1 (Just (Bool True)))
                     , j2 <- deduce (EvalTo e2 (Just (Int n)))
                     ]
                     ++
                     [ Node ("E-IfF",j) [j1,j2]
                     | j1 <- deduce (EvalTo e1 (Just (Bool False)))
                     , j2 <- deduce (EvalTo e3 (Just (Int n)))
                     ]
      e1 :+: e2   -> take 1
                     $ 
                     [ Node ("E-Plus",j) [j1,j2,j3]
                     | n1 <- ints (n^2)
                     , j1 <- deduce (EvalTo e1 (Just (Int n1)))
                     , n2 <- ints (n^2)
                     , j2 <- deduce (EvalTo e2 (Just (Int n2)))
                     , j3 <- deduce (Plus n1 n2 n)
                     ]
      e1 :-: e2   -> take 1
                     $ 
                     [ Node ("E-Minus",j) [j1,j2,j3]
                     | n1 <- ints (n^2)
                     , j1 <- deduce (EvalTo e1 (Just (Int n1)))
                     , n2 <- ints (n^2)
                     , j2 <- deduce (EvalTo e2 (Just (Int n2)))
                     , j3 <- deduce (Minus n1 n2 n)
                     ]
      e1 :*: e2   -> take 1
                     $ 
                     [ Node ("E-Times",j) [j1,j2,j3]
                     | n1 <- ints (n^2)
                     , j1 <- deduce (EvalTo e1 (Just (Int n1)))
                     , n2 <- ints (n^2)
                     , j2 <- deduce (EvalTo e2 (Just (Int n2)))
                     , j3 <- deduce (Times n1 n2 n)
                     ]
      _           -> []
    Bool b -> case e of
      Val (Bool b')
        | b == b' -> [ Node ("E-Bool",j) []]
        | True    -> []
      e1 :<: e2   -> take 1 $ [ Node ("E-Lt",j) [j1,j2,j3]
                     | n1 <- ints maxBound
                     , j1 <- deduce (EvalTo e1 (Just (Int n1)))
                     , n2 <- ints maxBound
                     , j2 <- deduce (EvalTo e2 (Just (Int n2)))
                     , j3 <- deduce (LessThan n1 n2 True)
                     ]
      IF e1 e2 e3 -> take 1
                     $ 
                     [ Node ("E-IfT",j) [j1,j2]
                     | j1 <- deduce (EvalTo e1 (Just (Bool True)))
                     , j2 <- deduce (EvalTo e2 (Just (Bool b)))
                     ]
                     ++
                     [ Node ("E-IfF",j) [j1,j2]
                     | j1 <- deduce (EvalTo e1 (Just (Bool False)))
                     , j2 <- deduce (EvalTo e3 (Just (Bool b)))
                     ]
      _           -> []
  Plus k m n     -> [ Node ("B-Plus",j) []  | k+m == n ]
  Minus k m n    -> [ Node ("B-Minus",j) [] | k-m == n ]
  Times k m n    -> [ Node ("B-Times",j) [] | k*m == n ]
  LessThan p q r -> [ Node ("B-Lt",j) []    | (p<q) == r ]

ints :: Int -> [Int]
ints m = takeWhile ((abs m >=) . abs) $ tail $ [0..] >>= \n -> [f n | f <- [id,negate]]

session,session' :: IO ()
session  = sessionGen  ("EvalML1Err> ",deduce)
session' = sessionGen' ("EvalML1Err> ",deduce)
