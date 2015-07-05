module Language.BCoPL.ReduceNatExp (
    -- * Types
    Judge(OnNat,ReduceTo)
    -- * deducers
  , deduceOne
  ) where

import Control.Applicative ((<|>))

import Language.BCoPL.Nat (Nat(..))
import qualified Language.BCoPL.Nat as Nat (Judge(..),deduce)
import Language.BCoPL.EvalNatExp (Exp(..))
import Language.BCoPL.Derivation (Tree(..),Derivation,Deducer,derivation)

import Debug.Trace (trace)

data Judge = OnNat Nat.Judge
           | ReduceTo Exp Exp
           | ReduceToOne Exp Exp  -- only for display
           | ReduceToDet Exp Exp  -- only for display

toOne :: Judge -> Judge
toOne (ReduceTo e1 e2) = ReduceToOne e1 e2
toDet :: Judge -> Judge
toDet (ReduceTo e1 e2) = ReduceToDet e1 e2

instance Show Judge where
  show (OnNat jn)          = show jn
  show (ReduceTo e1 e2)    = show e1 ++ " ->* " ++ show e2
  show (ReduceToOne e1 e2) = show e1 ++ " --> " ++ show e2
  show (ReduceToDet e1 e2) = show e1 ++ " ->d " ++ show e2

toJudge :: Derivation Nat.Judge -> Derivation Judge
toJudge (Node (s,nj) ts) = Node (s,OnNat nj) (map toJudge ts)

deduceOne :: Deducer Judge
deduceOne j = case j of
  OnNat nj              -> map toJudge (Nat.deduce nj)
  ReduceTo exp1 exp2 -> case exp2 of
    Nat n3             -> case exp1 of
      Nat n1 :+: Nat n2  -> Nat.deduce (Nat.Plus n1 n2 n3)  >>= \ j1 ->
                            [Node ("R-Plus",toOne j) [toJudge j1]]
      Nat n1 :*: Nat n2  -> Nat.deduce (Nat.Times n1 n2 n3) >>= \ j1 ->
                            [Node ("R-Times",toOne j) [toJudge j1]]
    e1' :+: e2'        -> case exp1 of
      e1 :+: e2
        | e2 == e2'      -> deduceOne (ReduceTo e1 e1')     >>= \ j1 ->
                            [Node ("R-PlusL",toOne j) [j1]]
        | e1 == e1'      -> deduceOne (ReduceTo e2 e2')     >>= \ j1 ->
                            [Node ("R-PlusR",toOne j) [j1]]
      _                  -> []
    e1' :*: e2'        -> case exp1 of
      e1 :*: e2
        | e2 == e2'      -> deduceOne (ReduceTo e1 e1')     >>= \ j1 ->
                            [Node ("R-TimesL",toOne j) [j1]]
        | e1 == e1'      -> deduceOne (ReduceTo e2 e2')     >>= \ j1 ->
                            [Node ("R-TimesR",toOne j) [j1]]
      _                  -> []

deduceMulti :: Deducer Judge -> Deducer Judge
deduceMulti deduce1 j = case j of
  ReduceTo exp1 exp2
    | exp1 == exp2    -> [Node ("MR-Zero",j) []]
    | otherwise       -> (deduce1 (ReduceTo exp1 exp2)      >>= \ j1 ->
                          [Node ("MR-One",j) [j1]])
                         <|>
                         case exp2 of
    Nat n3              -> [(:+:),(:*:)]                    >>= \ op ->
                           [Z .. n3]                        >>= \ n1 ->
                           [Z .. n3]                        >>= \ n2 ->
                           let exp1' = (Nat n1 `op` Nat n2) in
                           deduce1 (ReduceTo exp1' exp2)    >>= \ j2 ->
                           deduceMulti deduce1 (ReduceTo exp1 exp1')
                                                            >>= \ j1 ->
                           [Node ("MR-Multi",j) [j1,j2]]
    _                   -> []

deduceDetL :: Deducer Judge
deduceDetL j = case j of
  OnNat nj           -> map toJudge (Nat.deduce nj)
  ReduceTo exp1 exp2 -> case exp1 of
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
  OnNat nj           -> map toJudge (Nat.deduce nj)
  ReduceTo exp1 exp2 -> case exp1 of
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

{-
deduceMulti :: Deducer Judge -> Deducer Judge
deduceMulti deduce j = case j of
  ReduceTo exp1 exp2
    | exp1 == exp2     -> [Node ("MR-Zero",j) []]
    | otherwise        -> [Node ("MR-One",j) [j'] | j' <- deduce (ReduceTo exp1 exp2)]
  _                    -> []
-}

displayDL = putStrLn . derivation deduceDetL 
displayDR = putStrLn . derivation deduceDetR
displayML = putStrLn . derivation (deduceMulti deduceDetL)
displayMR = putStrLn . derivation (deduceMulti deduceDetR)
displayM  = putStrLn . derivation (deduceMulti deduceOne)
display   = putStrLn . derivation deduceOne
