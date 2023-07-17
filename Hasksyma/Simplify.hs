{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      :  Hasksyma.Simplify
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Hasksyma.Simplify
  ( simplify,
    simplify',
    simplifyn,
    mapExp,
    fixExp,
    simp,
  ) where

import Hasksyma.Const ( IsConst, Const(..), isExact )
import Hasksyma.Eval
    ( liftNum,
      liftNum2,
      liftIntegral2,
      liftFractional,
      liftFractional2,
      liftFloating,
      liftFloating2,
      liftIntPow,
      liftFracPow )
import Hasksyma.Exp
    ( Exp(..),
      FloatBinop(..),
      FracBinop(..),
      NumBinop(..),
      NumUnop(..),

      isConstE )

-- | Fully simplify an expression.
simplify :: (Eq a, Num a, IsConst a) => Exp a -> Exp a
simplify e | e' == e   = e
           | otherwise = simplify e'
  where
    e' = mapExp simp e

-- | Fully simplify an expression.
simplify' :: (Eq a, IsConst a) => Exp a -> Exp a
simplify' e = fixExp simp e

-- | Perform @n@ simplifcation steps on an expression.
simplifyn :: (Eq a, Num a, IsConst a) => Int -> Exp a -> Exp a
simplifyn 0 e             = e
simplifyn n e | e' == e   = e
              | otherwise = simplifyn (n-1) e'
  where
    e' = mapExp simp e

-- | Recursively apply a function to an expression and its sub-expressions.
mapExp :: (Eq a, IsConst a) => (Exp a -> Exp a) -> Exp a -> Exp a
mapExp _ e@Undefined{}        = e
mapExp _ e@Infty{}            = e
mapExp _ e@NegInfty{}         = e
mapExp _ e@ConstE{}           = e
mapExp _ e@VarE{}             = e
mapExp f (NumUnopE op x)      = f (NumUnopE op (mapExp f x))
mapExp f (FracUnopE op x)     = f (FracUnopE op (mapExp f x))
mapExp f (FloatUnopE op x)    = f (FloatUnopE op (mapExp f x))
mapExp f (NumBinopE op x y)   = f (NumBinopE op (mapExp f x) (mapExp f y))
mapExp f (IntPowE x n)        = f (IntPowE (mapExp f x) n)
mapExp f (FracPowE x n)       = f (FracPowE (mapExp f x) n)
mapExp f (IntBinopE op x y)   = f (IntBinopE op (mapExp f x) (mapExp f y))
mapExp f (FracBinopE op x y)  = f (FracBinopE op (mapExp f x) (mapExp f y))
mapExp f (FloatBinopE op x y) = f (FloatBinopE op (mapExp f x) (mapExp f y))

-- | Recursively apply a function to an expression and its sub-expressions until
-- reaching a fixed point.
fixExp :: (Eq a, IsConst a) => (Exp a -> Exp a) -> Exp a -> Exp a
fixExp _ e@Undefined{} = e
fixExp _ e@Infty{}     = e
fixExp _ e@NegInfty{}  = e
fixExp _ e@ConstE{}    = e
fixExp _ e@VarE{}      = e

fixExp f e@(NumUnopE op x)
    | e' == e   = e
    | otherwise = fixExp f e'
  where
    x' = fixExp f x
    e' = f (NumUnopE op x')

fixExp f e@(FracUnopE op x)
    | e' == e   = e
    | otherwise = fixExp f e'
  where
    x' = fixExp f x
    e' = f (FracUnopE op x')

fixExp f e@(FloatUnopE op x)
    | e' == e   = e
    | otherwise = fixExp f e'
  where
    x' = fixExp f x
    e' = f (FloatUnopE op x')

fixExp f e@(NumBinopE op x y)
    | e' == e   = e
    | otherwise = fixExp f e'
  where
    x' = fixExp f x
    y' = fixExp f y
    e' = f (NumBinopE op x' y')

fixExp f e@(IntPowE x n)
    | e' == e   = e
    | otherwise = fixExp f e'
  where
    x' = fixExp f x
    e' = f (IntPowE x' n)

fixExp f e@(FracPowE x n)
    | e' == e   = e
    | otherwise = fixExp f e'
  where
    x' = fixExp f x
    e' = f (FracPowE x' n)

fixExp f e@(IntBinopE op x y)
    | e' == e   = e
    | otherwise = fixExp f e'
  where
    x' = fixExp f x
    y' = fixExp f y
    e' = f (IntBinopE op x' y')

fixExp f e@(FracBinopE op x y)
    | e' == e   = e
    | otherwise = fixExp f e'
  where
    x' = fixExp f x
    y' = fixExp f y
    e' = f (FracBinopE op x' y')

fixExp f e@(FloatBinopE op x y)
    | e' == e   = e
    | otherwise = fixExp f e'
  where
    x' = fixExp f x
    y' = fixExp f y
    e' = f (FloatBinopE op x' y')

-- | One-step expression simplification.
simp :: (Eq a, IsConst a) => Exp a -> Exp a
simp (NumUnopE Neg (NumUnopE Neg x)) = x

simp (NumBinopE Add x y)
  | x == 0  = y
  | y == 0  = x
  | x == y  = 2 * x
  | y == -x = 0

-- Make constant in addition the last term
simp (NumBinopE Add n@ConstE{} x) | not (isConstE x) =
    x + n

simp (NumBinopE Add (NumBinopE Add x (ConstE n)) (ConstE m)) | isExact y =
    x + ConstE y
  where
    y = n + m

simp (NumBinopE Add x (NumBinopE Add y n@ConstE{})) =
    (x + y) + n

simp (NumBinopE Add (NumBinopE Add x n@ConstE{}) y) | not (isConstE y) =
    (x + y) + n

simp (NumBinopE Sub x y)
  | x == 0 = -y
  | y == 0 = x
  | x == y = 0

simp (NumBinopE Mul x y)
  | x == 0    = 0
  | y == 0    = 0
  | x == 1    = y
  | y == 1    = x
  | x == y    = IntPowE x 2

simp (NumBinopE Mul x (FracBinopE FDiv y x')) | x' == x =
    y

simp (NumBinopE Mul (FracBinopE FDiv y x) x') | x' == x =
    y

-- Make constant in multiplication the first term
simp (NumBinopE Mul x n@ConstE{}) | not (isConstE x) =
    n * x

simp (NumBinopE Mul (ConstE n) (NumBinopE Mul (ConstE m) x)) | isExact y =
    ConstE y * x
  where
    y = n * m

simp (NumBinopE Mul (NumBinopE Mul n@ConstE{} x) y) =
    n * (x * y)

simp (NumBinopE Mul (IntPowE x n) (FracPowE y m)) =
    NumBinopE Mul (FracPowE x n) (FracPowE y m)

simp (NumBinopE Mul (FracPowE x n) (IntPowE y m)) =
    NumBinopE Mul (FracPowE x n) (FracPowE y m)

simp (NumBinopE Mul (FracPowE x n) (FracPowE x' m)) | x' == x =
    FracPowE x (n + m)

simp (IntPowE x 1) = x

simp (IntPowE (ConstE x) n) = ConstE (x ^ n)

simp (FracPowE x 1) = x

simp (FracPowE (ConstE x) n) = ConstE (x ^^ n)

simp (FracBinopE FDiv x y)
  | x == 0 && y == 0 = Undefined
  | x == 0           = 0
  | y == 0           = Infty
  | x == 1           = FracPowE y (-1)
  | y == 1           = x
  | x == y           = 1

simp (FracBinopE FDiv (NumBinopE Mul x y) x') | x' == x =
    y

simp (FracBinopE FDiv (NumBinopE Mul y x) x') | x' == x =
    y

simp (FloatBinopE Pow e (ConstE (IntegerC n))) = FracPowE e n

simp (FloatBinopE Pow x y)
  | x == 0 && y == 0 = Undefined
  | x == 0           = 0
  | y == 0           = 1
  | y == 1           = x
  | y == -1          = FracBinopE FDiv 1 x

simp (NumUnopE op x)      = liftNum op x
simp (FracUnopE op x)     = liftFractional op x
simp (FloatUnopE op x)    = liftFloating op x
simp (NumBinopE op x y)   = liftNum2 op x y
simp (IntPowE e n)        = liftIntPow e n
simp (FracPowE e n)       = liftFracPow e n
simp (IntBinopE op x y)   = liftIntegral2 op x y
simp (FloatBinopE op x y) = liftFloating2 op x y
simp (FracBinopE op x y)  = liftFractional2 op x y

simp e = e
