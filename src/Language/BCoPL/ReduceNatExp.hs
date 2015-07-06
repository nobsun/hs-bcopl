module Language.BCoPL.ReduceNatExp (
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

import Language.BCoPL.Nat (Nat(..))
import qualified Language.BCoPL.Nat as Nat (Judge(..),deduce)
import Language.BCoPL.EvalNatExp (Exp(..))
import Language.BCoPL.Derivation (Tree(..),Derivation,Deducer,sessionGen,sessionGen')

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
    Nat n3             -> case exp1 of
      Nat n1 :+: Nat n2  -> Nat.deduce (Nat.Plus n1 n2 n3)  >>= \ j1 ->
                            [Node ("R-Plus",j) [toJudge j1]]
      Nat n1 :*: Nat n2  -> Nat.deduce (Nat.Times n1 n2 n3) >>= \ j1 ->
                            [Node ("R-Times",j) [toJudge j1]]
      _                  -> []
    e1' :+: e2'        -> case exp1 of
      e1 :+: e2
        | e2 == e2'      -> deduceOne (ReduceTo e1 e1')     >>= \ j1 ->
                            [Node ("R-PlusL",j) [j1]]
        | e1 == e1'      -> deduceOne (ReduceTo e2 e2')     >>= \ j1 ->
                            [Node ("R-PlusR",j) [j1]]
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
                          [Node ("MR-One",toOne j) [j1]])
                         ++
                         case exp2 of
    Nat n3              -> case exp1 of
      e1 :+: e2           -> [ Node ("MR-Multi",j) [j1,j2]
                             | n1 <- [Z .. n3]      
                             , n2 <- [Z .. n3]
                             , let exp1' = Nat n1 :+: Nat n2
                             , _ <- deduce1 (ReduceTo exp1' exp2)
                             , j2 <- deduceMulti deduce1 (ReduceTo e2 (Nat n2))
                             , j1 <- deduceMulti deduce1 (ReduceTo e1 (Nat n1))
                             ]
      e1 :*: e2           -> case n3 of
        Z                   -> [ Node ("MR-Multi",j) [j1,j2]
                               | j1 <- deduceMulti deduce1 (ReduceTo e1 (Nat Z))
                               , n2 <- [Z ..]
                               , j2 <- deduceMulti deduce1 (ReduceTo e2 (Nat n2))
                               ]
                               ++
                               [ Node ("MR-Multi",j) [j1,j2]
                               | j2 <- deduceMulti deduce1 (ReduceTo e1 (Nat Z))
                               , n1 <- [Z ..]
                               , j1 <- deduceMulti deduce1 (ReduceTo e2 (Nat n1))
                               ]
        _                   -> [ Node ("MR-Multi",j) [j1,j2]
                               | n1 <- [S(Z) .. n3]      
                               , n2 <- [S(Z) .. n3]
                               , let exp1' = Nat n1 :*: Nat n2
                               , _  <- deduce1 (ReduceTo exp1' exp2)
                               , j2 <- deduceMulti deduce1 (ReduceTo e2 (Nat n2))
                               , j1 <- deduceMulti deduce1 (ReduceTo e1 (Nat n1))
                               ]
      _                   -> []
    _                   -> []
  _                   -> error $ show j

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
