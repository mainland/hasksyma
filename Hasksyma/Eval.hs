{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      :  Hasksyma.Eval
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Hasksyma.Eval
  ( numunop,
    fracunop,
    floatunop,
    numbinop,
    intbinop,
    fracbinop,
    floatbinop,

    eval,

    liftNum,
    liftNum2,
    liftIntegral2,
    liftFractional,
    liftFractional2,
    liftFloating,
    liftFloating2,
    liftIntPow,
    liftFracPow,

    evalexact
  ) where

import Hasksyma.Const ( IsConst, Const(..), isExact)
import Hasksyma.Exp
    ( Exp(..),
      FloatBinop(..),
      FracBinop(..),
      IntBinop(..),
      NumBinop(..),
      FloatUnop(..),
      FracUnop(..),
      NumUnop(..) )

-- | Compute function corresponding 'NumUnop' operator
numunop :: NumUnop -> (forall a . Num a => a -> a)
numunop Neg    = negate
numunop Abs    = abs
numunop Signum = signum

-- | Compute function corresponding 'FracUnop' operator
fracunop :: FracUnop -> (forall a . Fractional a => a -> a)
fracunop Recip = recip

-- | Compute function corresponding 'FloatUnop' operator
floatunop :: FloatUnop -> (forall a . Floating a => a -> a)
floatunop Exp   = exp
floatunop Log   = log
floatunop Sqrt  = sqrt
floatunop Sin   = sin
floatunop Cos   = cos
floatunop Tan   = tan
floatunop Asin  = asin
floatunop Acos  = acos
floatunop Atan  = atan
floatunop Sinh  = sinh
floatunop Cosh  = cosh
floatunop Tanh  = tanh
floatunop Asinh = asinh
floatunop Acosh = acosh
floatunop Atanh = atanh

-- | Compute function corresponding 'NumBinop' operator
numbinop :: NumBinop -> (forall a . Num a => a -> a -> a)
numbinop Add = (+)
numbinop Sub = (-)
numbinop Mul = (*)

-- | Compute function corresponding 'IntBinop' operator
intbinop :: IntBinop -> (forall a . Integral a => a -> a -> a)
intbinop Quot = quot
intbinop Rem  = rem
intbinop Div  = div
intbinop Mod  = mod

-- | Compute function corresponding 'FracBinop' operator
fracbinop :: FracBinop -> (forall a . Fractional a => a -> a -> a)
fracbinop FDiv = (/)

-- | Compute function corresponding 'floatbinop' operator
floatbinop :: FloatBinop -> (forall a . Floating a => a -> a -> a)
floatbinop Pow     = (**)
floatbinop Root    = \t u -> t ** recip u
floatbinop LogBase = logBase

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

-- | Lift a 'NumUnop' operator to an @'Exp' a@, reducing constants when possible
-- while preserving exactness.
liftNum :: (IsConst a, Num a)
        => NumUnop
        -> Exp a
        -> Exp a
liftNum op (ConstE x) | isExact y = ConstE y
  where
    y = numunop op x

liftNum op e = NumUnopE op e

-- | Lift a 'NumBinop' operator to an @'Exp' a@, reducing constants when possible
-- while preserving exactness.
liftNum2 :: (IsConst a, Num a)
         => NumBinop
         -> Exp a
         -> Exp a
         -> Exp a
liftNum2 op (ConstE x) (ConstE y) | isExact z = ConstE z
  where
    z = numbinop op x y

liftNum2 op e1 e2 = NumBinopE op e1 e2

-- | Lift a 'IntBinop' operator to an @'Exp' a@, reducing constants when
-- possible while preserving exactness.
liftIntegral2 :: (IsConst a, Integral a)
              => IntBinop
              -> Exp a
              -> Exp a
              -> Exp a
liftIntegral2 op (ConstE x) (ConstE y) | isExact z = ConstE z
  where
    z = intbinop op x y

liftIntegral2 op e1 e2 = IntBinopE op e1 e2

-- | Lift a 'FracUnop' operator to an @'Exp' a@, reducing constants when
-- possible while preserving exactness.
liftFractional :: (IsConst a, Fractional a, Eq a)
               => FracUnop
               -> Exp a
               -> Exp a
liftFractional op (ConstE x) | (not (isRecip op) || x /= 0) && isExact y = ConstE y
  where
    y = fracunop op x

    isRecip :: FracUnop -> Bool
    isRecip Recip = True

liftFractional op e = FracUnopE op e

-- | Lift a 'FracBinop' operator to an @'Exp' a@, reducing constants when
-- possible while preserving exactness.
liftFractional2 :: (IsConst a, Eq a, Fractional a)
                => FracBinop
                -> Exp a
                -> Exp a
                -> Exp a
liftFractional2 op (ConstE x) (ConstE y) | (not (isFDiv op) || y /= 0) && isExact z = ConstE z
  where
    z = fracbinop op x y

    isFDiv :: FracBinop -> Bool
    isFDiv FDiv = True

liftFractional2 op e1 e2 = FracBinopE op e1 e2

-- | Lift a 'FloatUnop' operator to an @'Exp' a@, reducing constants when
-- possible while preserving exactness.
liftFloating :: (IsConst a, Floating a, Floating (Const a))
             => FloatUnop
             -> Exp a
             -> Exp a
liftFloating op (ConstE x) | isExact y = ConstE y
  where
    y = floatunop op x

liftFloating op e = FloatUnopE op e

-- | Lift a 'FloatBinop' operator to an @'Exp' a@, reducing constants when
-- possible while preserving exactness.
liftFloating2 :: (IsConst a, Floating a, Floating (Const a))
              => FloatBinop
              -> Exp a
              -> Exp a
              -> Exp a
liftFloating2 op (ConstE x) (ConstE y) | isExact z = ConstE z
  where
    z = floatbinop op x y

liftFloating2 op e1 e2 = FloatBinopE op e1 e2

-- | Lift operation of raising a number to an integral power to an @'Exp' a@,
-- reducing constants when possible while preserving exactness.
liftIntPow :: (IsConst a, Num a, Eq a)
           => Exp a
           -> Integer
           -> Exp a
liftIntPow (ConstE x) n | (x /= 0 || n /= 0) && isExact z = ConstE z
  where
    z = x ^ n

liftIntPow e n = IntPowE e n

-- | Lift operation of raising a number to a non-negative integral power to an
-- @'Exp' a@, reducing constants when possible while preserving exactness.
liftFracPow :: (IsConst a, Fractional a, Eq a)
            => Exp a
            -> Integer
            -> Exp a
liftFracPow (ConstE x) n | (x /= 0 || n > 0) && isExact z = ConstE z
  where
    z = x ^^ n

liftFracPow e n = FracPowE e n

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
