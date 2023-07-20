{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

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

import Data.Ratio ( denominator, numerator )

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
      FloatUnop(..),
      FracBinop(..),
      FracUnop(..),
      NumBinop(..),
      NumUnop(..))

-- | Fully simplify an expression.
simplify :: (Eq a, Num a, IsConst a) => Exp a -> Exp a
simplify e | e' == e   = e
           | otherwise = simplify e'
  where
    e' = mapExp simp e

-- | Fully simplify an expression.
simplify' :: (Eq a, Num a, IsConst a) => Exp a -> Exp a
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

-- | A n expression consisting of exponentiation
data Pow a where
    IntPow   :: Num a => Exp a -> Integer -> Pow a
    FracPow  :: Fractional a => Exp a -> Integer -> Pow a
    FloatPow :: (Floating a, Floating (Const a)) => Exp a -> Exp a -> Pow a

base :: Pow a -> Exp a
base (IntPow e _)   = e
base (FracPow e _)  = e
base (FloatPow e _) = e

pow :: (Eq a, Num a, IsConst a) => Exp a -> Maybe (Pow a)
pow e@VarE{}               = Just (IntPow e 1)
pow (IntPowE e n)          = Just (IntPow e n)
pow (FracPowE e n)         = Just (FracPow e n)
pow (FracUnopE Recip e)    = Just (FracPow e (-1))
pow (FloatUnopE Exp n)     = Just (FloatPow (ConstE E) n)
pow (FloatUnopE Sqrt e)    = Just (FloatPow e (1/2))
pow (FloatBinopE Pow e n)  = Just (FloatPow e n)
pow (FloatBinopE Root e n) = Just (FloatPow e (1/n))
pow _                      = Nothing

joinPowWith :: (Eq a, IsConst a)
            => (Pow a -> Pow a -> b)
            -> Pow a
            -> Pow a
            -> b
joinPowWith f x@IntPow{}   y@IntPow{}   = f x y
joinPowWith f x@FracPow{}  y@FracPow{}  = f x y
joinPowWith f x@FloatPow{} y@FloatPow{} = f x y

joinPowWith f (IntPow e1 n)   (FracPow e2 m)  = f (FracPow e1 n) (FracPow e2 m)
joinPowWith f (FracPow e1 n)  (IntPow e2 m)   = f (FracPow e1 n) (FracPow e2 m)
joinPowWith f (IntPow e1 n)   (FloatPow e2 m) = f (FloatPow e1 (fromInteger n)) (FloatPow e2 m)
joinPowWith f (FloatPow e1 n) (IntPow e2 m)   = f (FloatPow e1 n) (FloatPow e2 (fromInteger m))

joinPowWith f (FracPow e1 n)  (FloatPow e2 m) = f (FloatPow e1 (fromInteger n)) (FloatPow e2 m)
joinPowWith f (FloatPow e1 n) (FracPow e2 m)  = f (FloatPow e1 n) (FloatPow e2 (fromInteger m))

sumbefore :: (Eq a, Num a, IsConst a) => Exp a -> Exp a -> Bool
sumbefore ConstE{}           ConstE{}           = False
sumbefore _                  ConstE{}           = True
sumbefore (VarE x)           (VarE y)           = x < y
sumbefore (NumUnopE op1 _)   (NumUnopE op2 _)   = op1 < op2
sumbefore (FracUnopE op1 _)  (FracUnopE op2 _)  = op1 < op2
sumbefore (FloatUnopE op1 _) (FloatUnopE op2 _) = op1 < op2

sumbefore (NumBinopE Mul ConstE{} x) (NumBinopE Mul ConstE{} y) = x `sumbefore` y
sumbefore (NumBinopE Mul ConstE{} x) y                          = x `sumbefore` y
sumbefore x                          (NumBinopE Mul ConstE{} y) = x `sumbefore` y

sumbefore (pow -> Just p1) (pow -> Just p2)
    | base p1 == base p2 = joinPowWith go p1 p2
    | otherwise          = base p1 `sumbefore` base p2
  where
    go (IntPow _ n)   (IntPow _ m)   = n < m
    go (FracPow _ n)  (FracPow _ m)  = n < m
    go (FloatPow _ n) (FloatPow _ m) = sumbefore n m
    go _              _              = False

sumbefore _ _ = False

prodbefore :: (Eq a, Num a, IsConst a) => Exp a -> Exp a -> Bool
prodbefore ConstE{}           ConstE{}           = False
prodbefore ConstE{}           _                  = True
prodbefore (VarE x)           (VarE y)           = x < y
prodbefore (NumUnopE op1 _)   (NumUnopE op2 _)   = op1 < op2
prodbefore (FracUnopE op1 _)  (FracUnopE op2 _)  = op1 < op2
prodbefore (FloatUnopE op1 _) (FloatUnopE op2 _) = op1 < op2

prodbefore (pow -> Just p1) (pow -> Just p2)
    | base p1 == base p2 = joinPowWith go p1 p2
    | otherwise          = base p1 `prodbefore` base p2
  where
    go (IntPow _ n)   (IntPow _ m)   = n < m
    go (FracPow _ n)  (FracPow _ m)  = n < m
    go (FloatPow _ n) (FloatPow _ m) = prodbefore n m
    go _              _              = False

prodbefore _ _ = False

-- | One-step expression simplification.
simp :: forall a . (Eq a, Num a, IsConst a) => Exp a -> Exp a
simp (NumUnopE Neg (NumUnopE Neg x)) = x

simp (NumBinopE Add x y)
  | x == 0  = y
  | y == 0  = x
  | x == y  = 2 * x
  | y == -x = 0

-- | Reorder terms in sum
simp (NumBinopE Add x y) | y `sumbefore` x =
    y + x

simp (NumBinopE Add (NumBinopE Add x y) z) | z `sumbefore` y =
    x + z + y

-- Reassociate
simp (NumBinopE Add x (NumBinopE Add y z)) =
    x + y + z

-- Combine constants
simp (NumBinopE Add (NumBinopE Add x (ConstE n)) (ConstE m)) | isExact y =
    x + ConstE y
  where
    y = n + m

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

-- | Reorder terms in product
simp (NumBinopE Mul x y) | y `prodbefore` x =
    y * x

simp (NumBinopE Mul (NumBinopE Mul x y) z) | z `prodbefore` y =
    x * z * y

-- Reassociate
simp (NumBinopE Mul x (NumBinopE Mul y z)) =
    x * y * z

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

-- Simplify exponentiation
simp (NumBinopE Mul (FracPowE x n) y) | n < 0 =
    y / IntPowE x (-n)

simp (NumBinopE Mul (pow -> Just p1) (pow -> Just p2)) | base p1 == base p2 =
    joinPowWith mulPowers p1 p2

simp (NumBinopE Mul (NumBinopE Mul e (pow -> Just p1)) (pow -> Just p2)) | base p1 == base p2 =
    NumBinopE Mul e $ joinPowWith mulPowers p1 p2

simp (FracBinopE FDiv (pow -> Just p1) (pow -> Just p2)) | base p1 == base p2 =
    joinPowWith go p1 p2
  where
    go (IntPow x n)   (IntPow _ m)   = FracPowE x (n - m)
    go (FracPow x n)  (FracPow _ m)  = FracPowE x (n - m)
    go (FloatPow x n) (FloatPow _ m) = FloatBinopE Pow x (n - m)
    go _              _              = error "can't happen"

simp (pow -> Just p) = go p
  where
    go :: Pow a -> Exp a
    go (IntPow x n)
      | x == 0 && n == 0 = Undefined
      | n == 0           = 1
      | n == 1           = x

    go (IntPow (pow -> Just p1) n) =
        case p1 of
          IntPow x m   -> IntPowE x (n*m)
          FracPow x m  -> FracPowE x (n*m)
          FloatPow x m -> FloatBinopE Pow x (fromInteger n*m)

    go (IntPow x n) =
        liftIntPow x n

    go (FracPow x n)
      | x == 0 && n == 0 = Undefined
      | n == 0           = 1
      | n == 1           = x
      | n >= 0           = IntPowE x n

    go (FracPow (pow -> Just p1) n) =
        case p1 of
          IntPow x m   -> FracPowE x (n*m)
          FracPow x m  -> FracPowE x (n*m)
          FloatPow x m -> FloatBinopE Pow x (fromInteger n*m)

    go (FracPow x n) =
        liftFracPow x n

    go (FloatPow (ConstE E) (FloatUnopE Log x)) =
        x

    go (FloatPow x (ConstE (IntegerC n))) =
        FracPowE x n

    go (FloatPow x (ConstE (RationalC n)))
        | denominator n == 1 = FracPowE x (numerator n)

    go (FloatPow e1 e2) = liftFloating2 Pow e1 e2

-- Simplify logs
simp (FloatUnopE Log x)
    | x == 1 = 0

simp (FloatUnopE Log (pow -> Just p)) | base p == ConstE E = go p
  where
    go (IntPow _ n)   = fromInteger n
    go (FracPow _ n)  = fromInteger n
    go (FloatPow _ n) = n

simp (FloatBinopE LogBase (ConstE E) x) =
    log x

simp (FloatBinopE LogBase _ x)
    | x == 1 = 0

simp (FloatBinopE LogBase b (pow -> Just p)) | base p == b = go p
  where
    go (IntPow _ n)   = fromInteger n
    go (FracPow _ n)  = fromInteger n
    go (FloatPow _ n) = n

-- Combine logs
simp (NumBinopE Add (FloatUnopE Log x) (FloatUnopE Log y)) =
    FloatUnopE Log (x * y)

simp (NumBinopE Add (FloatBinopE LogBase b x) (FloatBinopE LogBase b' y)) | b' == b =
    FloatBinopE LogBase b (x * y)

simp (NumBinopE Sub (FloatUnopE Log x) (FloatUnopE Log y)) =
    FloatUnopE Log (x / y)

simp (NumBinopE Sub (FloatBinopE LogBase b x) (FloatBinopE LogBase b' y)) | b' == b =
    FloatBinopE LogBase b (x / y)

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

-- | Multiply exponents with equal bases
mulPowers :: (Eq a, IsConst a) => Pow a -> Pow a -> Exp a
mulPowers (IntPow x n)   (IntPow _ m)   = IntPowE x (n + m)
mulPowers (FracPow x n)  (FracPow _ m)  = FracPowE x (n + m)
mulPowers (FloatPow x n) (FloatPow _ m) = FloatBinopE Pow x (n + m)
mulPowers _              _              = error "can't happen"
