{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NPlusKPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.BCoPL.Nat (
    ) where

data Nat = Z | S Nat deriving (Eq,Ord)

instance Show Nat where
  show Z     = "Z"
  show (S n) = "S("++show n++")"

data Nat' (n :: Nat) where
  Z' :: Nat' Z
  S' :: Nat' n -> Nat' (S n)

instance Show (Nat' Z) where
  show Z' = "Z"

instance Show (Nat' n) => Show (Nat' (S n)) where
  show (S' n) = "S("++show n++")"

data a :=: b where
  Refl  :: a :=: a
  Symm  :: a :=: b -> b :=: a
  Tran  :: a :=: b -> b :=: c -> a :=: c

type family (:+:) a b where
  Z :+: n   = n
  S m :+: n = S (m :+: n)

pZero :: Nat' a -> (Z :+: a) :=: a
pZero _ = Refl

pSucc :: Nat' n1 -> Nat' n2 -> Nat' n3 -> (n1 :+: n2) :=: n3 -> (S n1 :+: n2) :=: S n3
pSucc n1 n2 n3 premise = case premise of Refl -> Refl

z_plus_sssssz_is_sssssz :: Z :+: S(S(S(S(S Z)))) :=: S(S(S(S(S Z))))
z_plus_sssssz_is_sssssz = pZero (S'(S'(S'(S'(S' Z')))))

ssz_plus_sssz_is_sssssz :: S(S Z) :+: S(S(S Z)) :=: S(S(S(S(S Z))))
ssz_plus_sssz_is_sssssz = proof3
  where
    proof3 :: S(S Z) :+: S(S(S Z)) :=: S(S(S(S(S Z))))
    proof3 = pSucc (S' Z') (S'(S'(S' Z'))) (S'(S'(S'(S' Z')))) proof2
    proof2 :: S Z :+: S(S(S Z)) :=: S(S(S(S Z)))
    proof2 = pSucc Z' (S'(S'(S' Z'))) (S'(S'(S' Z'))) proof1
    proof1 :: Z :+: S(S(S Z)) :=: S(S(S Z))
    proof1 = pZero (S'(S'(S' Z')))

-- data Z
-- data S n

-- data Nat n where
--   Z :: Nat Z
--   S :: Nat n -> Nat (S n)

-- data a :=: b where
--   Refl  :: a :=: a
--   Symm  :: a :=: b -> b :=: a
--   Tran  :: a :=: b -> b :=: c -> a :=: c

-- type family (:+:) a b where
--   Z   :+: n = n
--   S m :+: n = S (m :+: n)

-- pZero :: Nat a -> (Z :+: a) :=: a
-- pZero _ = Refl

-- pSucc :: Nat n1 -> Nat n2 -> Nat n3 -> (n1 :+: n2) :=: n3 -> (S n1 :+: n2) :=: S n3
-- pSucc n1 n2 n3 premise = case premise of Refl -> Refl

-- z_plus_sssssz_is_sssssz :: Z :+: S(S(S(S(S Z)))) :=: S(S(S(S(S Z))))
-- z_plus_sssssz_is_sssssz = pZero (S(S(S(S(S Z)))))

-- ssz_plus_sssz_is_sssssz :: S(S Z) :+: S(S(S Z)) :=: S(S(S(S(S Z))))
-- ssz_plus_sssz_is_sssssz = proof3
--   where
--     proof3 :: S(S Z) :+: S(S(S Z)) :=: S(S(S(S(S Z))))
--     proof3 = pSucc (S Z) (S(S(S Z))) (S(S(S(S Z)))) proof2
--     proof2 :: S Z :+: S(S(S Z)) :=: S(S(S(S Z)))
--     proof2 = pSucc Z (S(S(S Z))) (S(S(S Z))) proof1
--     proof1 :: Z :+: S(S(S Z)) :=: S(S(S Z))
--     proof1 = pZero (S(S(S Z)))

{-
data Judge = Plus { k,m,n :: Nat }
           | Times { k,m,n :: Nat }
           deriving (Eq)

instance Show Judge where
  show (Plus k m n)  = show k ++ " plus " ++ show m ++ " is " ++ show n
  show (Times k m n) = show k ++ " times " ++ show m ++ " is " ++ show n

deduce :: Deducer Judge
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
-}
