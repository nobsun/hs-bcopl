{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
module Language.BCoPL.EvalNatExp where

import Language.BCoPL.Peano
import Language.BCoPL.Nat
import Language.BCoPL.Exp

data EvalTo (exp :: Exp) (n :: Nat) where
  EConst :: Nat' n -> EvalTo (ENat n) n
  EPlus  :: Exp' e1 -> Exp' e2 -> Nat' n1 -> Nat' n2 -> Nat' n3
         -> EvalTo e1 n1 -> EvalTo e2 n2 -> Plus n1 n2 n3
         -> EvalTo (e1 :＋ e2) n3
  ETimes :: Exp' e1 -> Exp' e2 -> Nat' n1 -> Nat' n2 -> Nat' n3
         -> EvalTo e1 n1 -> EvalTo e2 n2 -> Times n1 n2 n3
         -> EvalTo (e1 :× e2) n3

-- --------------------------------------------------

ex010801 :: EvalTo (ENat Z :＋ ENat (S(S Z))) (S(S Z))
ex010801 =  EPlus (ENat' Z') (ENat' (S'(S' Z'))) Z' (S'(S' Z')) (S'(S' Z'))
                  (EConst Z') 
                  (EConst (S'(S' Z')))
                  (PZero (S'(S' Z')))

ex010802 :: EvalTo (ENat (S(S Z)) :＋ ENat Z) (S(S Z))
ex010802 =  EPlus (ENat' (S'(S' Z'))) (ENat' Z') (S'(S' Z')) Z' (S'(S' Z'))
                  (EConst (S'(S' Z')))
                  (EConst Z') 
                  (PSucc (S' Z') Z' (S' Z') 
                         (PSucc Z' Z' Z' 
                                (PZero Z')))

ex010803 :: EvalTo ((ENat (S Z) :＋ ENat (S Z)) :＋ ENat (S Z)) (S(S(S Z)))
ex010803 = EPlus (ENat' (S' Z') :＋: ENat' (S' Z')) (ENat' (S' Z')) (S'(S' Z')) (S' Z') (S'(S'(S' Z')))
                 (EPlus (ENat' (S' Z')) (ENat' (S' Z')) (S' Z') (S' Z') (S'(S' Z'))
                        (EConst (S' Z'))
                        (EConst (S' Z'))
                        (PSucc Z' (S' Z') (S' Z')
                               (PZero (S' Z'))))
                 (EConst (S' Z'))
                 (PSucc (S' Z') (S' Z') (S' (S' Z'))
                        (PSucc Z' (S' Z') (S' Z')
                               (PZero (S' Z')))) 
                 
ex010804 :: EvalTo (ENat (S(S(S Z))) :＋ (ENat (S(S Z)) :× ENat (S Z))) (S(S(S(S(S Z)))))
ex010804 =  EPlus (ENat' (S'(S'(S' Z')))) (ENat' (S'(S' Z')) :×: ENat' (S' Z')) (S'(S'(S' Z'))) (S'(S' Z')) (S'(S'(S'(S'(S' Z')))))
                  (EConst (S'(S'(S' Z'))))
                  (ETimes (ENat' (S'(S' Z'))) (ENat' (S' Z')) (S'(S' Z')) (S' Z') (S'(S' Z'))
                          (EConst (S' (S' Z')))
                          (EConst (S' Z'))
                          (TSucc (S' Z') (S' Z') (S' Z') (S'(S' Z'))
                                 (TSucc Z' (S' Z') Z' (S' Z')
                                        (TZero (S' Z'))
                                        (PSucc Z' Z' Z'
                                               (PZero Z')))
                                 (PSucc Z' (S' Z') (S' Z')
                                        (PZero (S' Z')))))
                  (PSucc (S'(S' Z')) (S'(S' Z')) (S'(S'(S'(S' Z'))))
                         (PSucc (S' Z') (S'(S' Z')) (S'(S'(S' Z')))
                                (PSucc Z' (S'(S' Z')) (S'(S' Z'))
                                       (PZero (S'(S' Z'))))))

ex010805 :: EvalTo ((ENat (S(S Z)) :＋ ENat (S(S Z))) :× ENat Z) Z
ex010805 =  ETimes (ENat' (S'(S' Z')) :＋: ENat' (S'(S' Z'))) (ENat' Z') (S'(S'(S'(S' Z')))) Z' Z'
                   (EPlus (ENat' (S'(S' Z'))) (ENat' (S'(S' Z'))) (S'(S' Z')) (S'(S' Z')) (S'(S'(S'(S' Z'))))
                          (EConst (S'(S' Z')))
                          (EConst (S'(S' Z')))
                          (PSucc (S' Z') (S'(S' Z')) (S'(S'(S' Z')))
                                 (PSucc Z' (S'(S' Z')) (S'(S' Z'))
                                        (PZero (S'(S' Z'))))))
                   (EConst Z')
                   (TSucc (S'(S'(S' Z'))) Z' Z' Z'
                          (TSucc (S'(S' Z')) Z' Z' Z'
                                 (TSucc (S' Z') Z' Z' Z'
                                        (TSucc Z' Z' Z' Z'
                                               (TZero Z')
                                               (PZero Z'))
                                        (PZero Z'))
                                 (PZero Z'))
                          (PZero Z'))

ex010806 :: EvalTo (ENat Z :× (ENat (S(S Z)) :＋ ENat (S(S(Z))))) Z
ex010806 = ETimes (ENat' Z') (ENat' (S'(S' Z')) :＋: ENat' (S'(S' Z'))) Z' (S'(S'(S'(S' Z')))) Z'
                  (EConst Z')
                  (EPlus (ENat' (S'(S' Z'))) (ENat' (S'(S' Z'))) (S'(S' Z')) (S'(S' Z')) (S'(S'(S'(S' Z'))))
                         (EConst (S'(S' Z')))
                         (EConst (S'(S' Z')))
                         (PSucc (S' Z') (S'(S' Z')) (S'(S'(S' Z')))
                                (PSucc Z' (S'(S' Z')) (S'(S' Z'))
                                       (PZero (S'(S' Z'))))))
                  (TZero (S'(S'(S'(S' Z')))))
