{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      :  Hasksyma.Eval
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Hasksyma.Eval
  ( eval,

    evalexact
  ) where

import Hasksyma.Const ( IsConst )
import Hasksyma.Exp
    ( Exp(..),
      numunop,
      fracunop,
      floatunop,
      numbinop,
      intbinop,
      fracbinop,
      floatbinop,
      liftNum,
      liftNum2,
      liftIntegral2,
      liftFractional,
      liftFractional2,
      liftFloating,
      liftFloating2,
      liftIntPow,
      liftFracPow )

-- | Fully evaluate all closed subexpressions of an expression. Does not
-- preserve exactness.
eval :: (IsConst a, Eq a) => Exp a -> Exp a
eval e@Undefined{}           = e
eval e@Infty{}               = e
eval e@NegInfty{}            = e
eval e@ConstE{}              = e
eval e@VarE{}                = e
eval (NumUnopE op e)         = case eval e of
                                 ConstE x -> ConstE $ numunop op x
                                 e'       -> NumUnopE op e'
eval (FracUnopE op e)        = case eval e of
                                 ConstE x -> ConstE $ fracunop op x
                                 e'       -> FracUnopE op e'
eval (FloatUnopE op e)       = case eval e of
                                 ConstE x -> ConstE $ floatunop op x
                                 e'       -> FloatUnopE op e'
eval (NumBinopE op e1 e2)    = case (eval e1, eval e2) of
                                 (ConstE x, ConstE y) -> ConstE $ numbinop op x y
                                 (e1', e2')           -> NumBinopE op e1' e2'
eval (IntPowE e n)           = case eval e of
                                 ConstE x -> ConstE (x ^ n)
                                 e'       -> IntPowE e' n
eval (FracPowE e n)          = case eval e of
                                 ConstE x -> ConstE (x ^^ n)
                                 e'       -> IntPowE e' n
eval (IntBinopE op e1 e2)    = case (eval e1, eval e2) of
                                 (ConstE x, ConstE y) -> ConstE $ intbinop op x y
                                 (e1', e2')           -> IntBinopE op e1' e2'
eval (FracBinopE op e1 e2)   = case (eval e1, eval e2) of
                                 (ConstE x, ConstE y) -> ConstE $ fracbinop op x y
                                 (e1', e2')           -> FracBinopE op e1' e2'
eval (FloatBinopE op e1 e2)  = case (eval e1, eval e2) of
                                 (ConstE x, ConstE y) -> ConstE $ floatbinop op x y
                                 (e1', e2')           -> FloatBinopE op e1' e2'
eval e@DiffE{}               = e
eval e@IntE{}                = e

-- | Fully evaluate closed subexpressions of an expression when possible while
-- preserving exactness.
evalexact :: (IsConst a, Eq a) => Exp a -> Exp a
evalexact (IntPowE e n)           = liftIntPow (evalexact e) n
evalexact (FracPowE e n)          = liftFracPow (evalexact e) n
evalexact (NumUnopE op e)         = liftNum op (evalexact e)
evalexact (FracUnopE op e)        = liftFractional op (evalexact e)
evalexact (FloatUnopE op e)       = liftFloating op (evalexact e)
evalexact (NumBinopE op e1 e2)    = liftNum2 op (evalexact e1) (evalexact e2)
evalexact (IntBinopE op e1 e2)    = liftIntegral2 op (evalexact e1) (evalexact e2)
evalexact (FracBinopE op e1 e2)   = liftFractional2 op (evalexact e1) (evalexact e2)
evalexact (FloatBinopE op e1 e2)  = liftFloating2 op (evalexact e1) (evalexact e2)
evalexact e                       = e
