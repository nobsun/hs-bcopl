{-# LANGUAGE BangPatterns #-}
module Language.BCoPL.DataLevel.ReduceNatExp (
    -- * Types
    Judge(OnNat,ReduceTo)
    -- * Deducers
  , deduceOne
  , deduceDetL
  , deduceDetR
  , deduceMulti
    -- * Sessions
  , sessionDetL
  , sessionDetR
  , sessionMultiL
  , sessionMultiR
  , sessionMulti
  , sessionOne
  , sessionDetL'
  , sessionDetR'
  , sessionMultiL'
  , sessionMultiR'
  , sessionMulti'
  , sessionOne'
  ) where

import Control.Applicative ((<|>))

import Language.BCoPL.DataLevel.Nat (Nat(..))
import qualified Language.BCoPL.DataLevel.Nat as Nat (Judge(..),deduce)
import Language.BCoPL.DataLevel.Exp (Exp(..),operator,loperand,roperand)
import Language.BCoPL.DataLevel.Derivation (Tree(..),Derivation,Deducer,sessionGen,sessionGen')

data Judge = OnNat Nat.Judge
           | ReduceTo Exp Exp
           | ReduceToOne Exp Exp
           | ReduceToDet Exp Exp

toOne :: Judge -> Judge
toOne (ReduceTo e1 e2) = ReduceToOne e1 e2
toOne j                = j
toDet :: Judge -> Judge
toDet (ReduceTo e1 e2) = ReduceToDet e1 e2
toDet j                = j

instance Show Judge where
  show (OnNat jn)          = show jn
  show (ReduceTo e1 e2)    = unwords [show e1,"-*->",show e2]
  show (ReduceToOne e1 e2) = unwords [show e1,"--->",show e2]
  show (ReduceToDet e1 e2) = unwords [show e1,"-d->",show e2]

instance Read Judge where
  readsPrec _ s = case break ("-*->"==) (words s) of
    (es1,_:es2) -> [(ReduceTo (read (concat es1)) (read (concat es2)),"")]
    (es1,[])    -> case break ("--->"==) es1 of
      (es1',_:es2') -> [(ReduceToOne (read (concat es1')) (read (concat es2')),"")]
      (es1',[])     -> case break ("-d->"==) es1' of
        (es1'',_:es2'') -> [(ReduceToDet (read (concat es1'')) (read (concat es2'')),"")]
        _               -> error ("Invalid syntax for 'ReduceNatExp' judge: "++s)

toJudge :: Derivation Nat.Judge -> Derivation Judge
toJudge (Node (s,nj) ts) = Node (s,OnNat nj) (map toJudge ts)

deduceOne :: Deducer Judge
deduceOne j = case j of
  OnNat nj              -> map toJudge (Nat.deduce nj)
  ReduceTo _ _          -> deduceOne (toOne j)
  ReduceToOne exp1 exp2 -> case exp2 of
    Nat n3                -> case exp1 of
      Nat n1 :+: Nat n2     -> [ Node ("R-Plus",j) [toJudge j1]
                               | j1 <- Nat.deduce (Nat.Plus n1 n2 n3) ]
      Nat n1 :*: Nat n2     -> [ Node ("R-Times",j) [toJudge j1]
                               | j1 <- Nat.deduce (Nat.Times n1 n2 n3) ]
      _                     -> []
    e1' :+: e2'           -> case exp1 of
      e1 :+: e2
        | e2 == e2'         -> [ Node ("R-PlusL",j) [j1]
                               | j1 <- deduceOne (ReduceToOne e1 e1') ]
        | e1 == e1'         -> [ Node ("R-PlusR",j) [j1]
                               | j1 <- deduceOne (ReduceToOne e2 e2') ]
      _                     -> []
    e1' :*: e2'           -> case exp1 of
      e1 :*: e2
        | e2 == e2'         -> [ Node ("R-TimesL",j) [j1]
                               | j1 <- deduceOne (ReduceToOne e1 e1') ]
        | e1 == e1'         -> [ Node ("R-TimesR",j) [j1]
                               | j1 <- deduceOne (ReduceToOne e2 e2') ]
      _                     -> []

deduceMulti :: Deducer Judge -> Deducer Judge
deduceMulti deduce1 j@(ReduceTo exp1 exp2)
  = if exp1 == exp2 then [ Node ("MR-Zero",j) [] ]
    else case [ Node ("MR-One",j) [j'] | j' <- deduce1 j ] of
      d@(_:_) -> d
      []      -> case j of
        ReduceTo exp1 exp2
          | exp1 == exp2      -> [ Node ("MR-Zero",j) [] ]
          | not (isNormalForm exp1)
            && not (isNormalForm exp2)
            && (operator exp1 z z /= operator exp2 z z)
                 -> []
          | otherwise -> [ Node ("MR-Multi",j) [j1,j2]
                         | exp' <- genExps exp1 exp2
                         , j2   <- deduceMulti deduce1 $ ReduceTo exp' exp2
                         , j1   <- deduceMulti deduce1 $ ReduceTo exp1 exp'
                         ]
  where z = Nat Z

genExps :: Exp -> Exp -> [Exp]
genExps exp1 exp2
  | isNormalForm exp2 = case exp1 of
    Nat _ -> []
    _     -> case exp2 of
      Nat Z -> case exp1 of
        _ :+: _ -> [ Nat Z :+: Nat Z ]
        _ :*: _ -> [ Nat Z :*: Nat n | n <- [Z ..] ]
      n     -> case loperand exp1 of
        Nat n1 -> [ operator exp1 (Nat n1) (Nat n2) | n2 <- [S Z .. ] ]
        _      -> [ operator exp1 (Nat n1) (roperand exp1) | n1 <- [S Z .. ] ]
  | isDeltaRedex exp2 = case exp1 of
      Nat _  -> []
      _      -> case loperand exp1 of
        e1@(Nat _) 
           | e1 == loperand exp2
               -> [ operator exp1 e1 (roperand exp2) ]
           | otherwise 
               -> []
        e1     -> [ operator exp1 (loperand exp2) (roperand exp1) ]
  | otherwise         = case exp1 of
      Nat _  -> []
      _      -> case loperand exp1 of
        e1@(Nat _)
          | e1 == loperand exp2
               -> [ operator exp1 e1 (roperand exp2) ]
          | otherwise 
               -> []
        e1     -> [ operator exp1 (loperand exp2) (roperand exp1) ]

deduceDetL :: Deducer Judge
deduceDetL j = case j of
  ReduceTo _ _       -> deduceDetL (toDet j)
  OnNat nj           -> map toJudge (Nat.deduce nj)
  ReduceToDet exp1 exp2 -> case exp1 of
    e1 :+: e2          -> case e1 of
      Nat n1             -> case e2 of
        Nat n2             -> case exp2 of
          Nat n3             -> [Node ("DR-Plus",j) [toJudge j'] | j' <- Nat.deduce (Nat.Plus n1 n2 n3)]
          _                  -> []
        _                  -> case exp2 of
          Nat n1' :+: e2'
            | n1 == n1'      -> [Node ("DR-PlusR",j) [j'] | j' <- deduceDetL (ReduceTo e2 e2')]
          _                  -> []
      _                  -> case exp2 of
        e1' :+: e2'
          | e2 == e2'      -> [Node ("DR-PlusL",j) [j'] | j' <- deduceDetL (ReduceTo e1 e1')]
        _                  -> []
    e1 :*: e2          -> case e1 of
      Nat n1             -> case e2 of
        Nat n2             -> case exp2 of
          Nat n3             -> [Node ("DR-Times",j) [toJudge j'] | j' <- Nat.deduce (Nat.Times n1 n2 n3)]
          _                  -> []
        _                  -> case exp2 of
          Nat n1' :*: e2'
            | n1 == n1'      -> [Node ("DR-TimesR",j) [j'] | j' <- deduceDetL (ReduceTo e2 e2')]
          _                  -> []
      _                  -> case exp2 of
        e1' :*: e2'
          | e2 == e2'      -> [Node ("DR-TimesL",j) [j'] | j' <- deduceDetL (ReduceTo e1 e1')]
        _                  -> []
    _                  -> []
  _                  -> []

deduceDetR :: Deducer Judge
deduceDetR j = case j of
  ReduceTo _ _       -> deduceDetR (toDet j)
  OnNat nj           -> map toJudge (Nat.deduce nj)
  ReduceToDet exp1 exp2 -> case exp1 of
    e1 :+: e2          -> case e2 of
      Nat n2             -> case e1 of
        Nat n1             -> case exp2 of
          Nat n3             -> [Node ("DR-Plus",j) [toJudge j'] | j' <- Nat.deduce (Nat.Plus n1 n2 n3)]
          _                  -> []
        _                  -> case exp2 of
          e1' :+: Nat n2'
            | n2 == n2'      -> [Node ("DR-PlusL",j) [j'] | j' <- deduceDetR (ReduceTo e1 e1')]
          _                  -> []
      _                  -> case exp2 of
        e1' :+: e2'
          | e1 == e1'      -> [Node ("DR-PlusL",j) [j'] | j' <- deduceDetR (ReduceTo e2 e2')]
        _                  -> []
    e1 :*: e2          -> case e2 of
      Nat n2             -> case e1 of
        Nat n1             -> case exp2 of
          Nat n3             -> [Node ("DR-Times",j) [toJudge j'] | j' <- Nat.deduce (Nat.Times n1 n2 n3)]
          _                  -> []
        _                  -> case exp2 of
          e1' :*: Nat n2'
            | n2 == n2'      -> [Node ("DR-TimesL",j) [j'] | j' <- deduceDetR (ReduceTo e1 e1')]
          _                  -> []
      _                  -> case exp2 of
        e1' :*: e2'
          | e1 == e1'      -> [Node ("DR-TimesL",j) [j'] | j' <- deduceDetR (ReduceTo e2 e2')]
        _                  -> []
    _                  -> []
  _                  -> []


isNormalForm :: Exp -> Bool
isNormalForm (Nat _) = True
isNormalForm _       = False

isDeltaRedex :: Exp -> Bool
isDeltaRedex e = case e of
  (e1 :+: e2) -> isNormalForm e1 && isNormalForm e2
  (e1 :*: e2) -> isNormalForm e1 && isNormalForm e2
  _           -> False

sessionDetL,sessionDetR,sessionMultiL,sessionMultiR,sessionMulti,sessionOne :: IO ()
sessionDetL   = sessionGen ("ReduceDetL> ",deduceDetL)
sessionDetR   = sessionGen ("ReduceDetR> ",deduceDetR)
sessionMultiL = sessionGen ("ReduceMultiL> ",deduceMulti deduceDetL)
sessionMultiR = sessionGen ("ReduceMultiR> ",deduceMulti deduceDetR)
sessionMulti  = sessionGen ("ReduceMulti> ",deduceMulti deduceOne)
sessionOne    = sessionGen ("ReduceOne> ",deduceOne)

sessionDetL',sessionDetR',sessionMultiL',sessionMultiR',sessionMulti',sessionOne' :: IO ()
sessionDetL'   = sessionGen' ("ReduceDetL> ",deduceDetL)
sessionDetR'   = sessionGen' ("ReduceDetR> ",deduceDetR)
sessionMultiL' = sessionGen' ("ReduceMultiL> ",deduceMulti deduceDetL)
sessionMultiR' = sessionGen' ("ReduceMultiR> ",deduceMulti deduceDetR)
sessionMulti'  = sessionGen' ("ReduceMulti> ",deduceMulti deduceOne)
sessionOne'    = sessionGen' ("ReduceOne> ",deduceOne)

{-
S(Z) * S(Z) + S(Z) * S(Z) -*-> S(S(Z)) by MR-Multi {
  S(Z) * S(Z) + S(Z) * S(Z) -*-> S(Z) + S(Z) * S(Z) by MR-One {
    S(Z) * S(Z) + S(Z) * S(Z) ---> S(Z) + S(Z) * S(Z) by R-PlusL {
      S(Z) * S(Z) ---> S(Z) by R-Times {
        S(Z) times S(Z) is S(Z) by T-Succ {
          Z times S(Z) is Z by T-Zero {  } ;
          S(Z) plus Z is S(Z) by P-Succ {
            Z plus Z is Z by P-Zero {  }
          }
        }
      }
    }
  } ;
  S(Z) + S(Z) * S(Z) -*-> S(S(Z)) by MR-Multi {
    S(Z) + S(Z) * S(Z) -*-> S(Z) + S(Z) by MR-One {
      S(Z) + S(Z) * S(Z) ---> S(Z) + S(Z) by R-PlusR {
        S(Z) * S(Z) ---> S(Z) by R-Times {
          S(Z) times S(Z) is S(Z) by T-Succ {
            Z times S(Z) is Z by T-Zero {  } ;
            S(Z) plus Z is S(Z) by P-Succ {
              Z plus Z is Z by P-Zero {  }
            }
          }
        }
      }
    } ;
    S(Z) + S(Z) -*-> S(S(Z)) by MR-One {
      S(Z) + S(Z) ---> S(S(Z)) by R-Plus {
        S(Z) plus S(Z) is S(S(Z)) by P-Succ {
          Z plus S(Z) is S(Z) by P-Zero {  }
        }
      }
    }
  }
}

-}
