{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}

-- |
-- Module      :  Test.Eval
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Eval
  ( arbitraryConst,
    arbitraryExactConst,
    arbitraryClosedExp,

    DExp(..),
    ExactDExp(..),

    evalTests,

    wellDefined
  )
  where

import           Control.Applicative (Alternative, empty, (<|>))
import           Control.Monad       (forM_)
import           Test.Hspec          (Spec, describe, it)
import           Test.HUnit          ((@?=))
import           Test.QuickCheck     (Arbitrary (..), Gen, Positive (getPositive), Property,
                                      Testable (property), arbitraryBoundedEnum, discard, frequency,
                                      oneof, resize, sized, (===))

import           Hasksyma.Const      (Const (..), IsConst (fromConst))
import           Hasksyma.Eval       (eval, evalexact)
import           Hasksyma.Exp        (Exp (..), FloatBinop (..), FloatUnop (..), FracBinop (..),
                                      FracUnop (..), NumUnop (..))

-- | Select finite, well-scaled closed expressions for numerical properties.
-- The ranges deliberately sample less than the full mathematical domains.
-- Compare numerical values, since expression ordering only orders syntax.
wellDefined :: Exp Double -> Bool
wellDefined e = wd e && check e wellScaled
  where
    wd (NumUnopE Signum x)       = check x (>= 0.1)
    wd (IntPowE _ n)             = n > 0 && n <= 10
    wd (FracPowE x n)            = check x $ \a -> abs n <= 10 && (a /= 0 || n > 0)
    wd (FracUnopE Recip x)       = check x (/= 0)
    wd (FloatUnopE Log x)        = check x (>= 0.1)
    wd (FloatUnopE Exp x)        = check x (>= 0.1)
    wd (FloatUnopE Sqrt x)       = check x (>= 0)
    wd (FloatUnopE Sin x)        = check x $ \a -> a >= -pi && a <= pi
    wd (FloatUnopE Cos x)        = check x $ \a -> a >= -pi && a <= pi
    wd (FloatUnopE Tan x)        = check x $ \a -> a > -pi/2 && a < pi/2
    wd (FloatUnopE Asin x)       = check x $ \a -> a >= -1 && a <= 1
    wd (FloatUnopE Acos x)       = check x $ \a -> a >= -1 && a <= 1
    wd (FloatUnopE Sinh x)       = check x $ \a -> a >= -10 && a <= 10
    wd (FloatUnopE Cosh x)       = check x $ \a -> a >= -10 && a <= 10
    wd (FloatUnopE Acosh x)      = check x (>= 1)
    wd (FloatUnopE Atanh x)      = check x $ \a -> a > -1 && a < 1
    wd (FracBinopE FDiv _ y)     = check y (/= 0)
    wd (FloatBinopE Pow x y)     = check2 x y $ \a b ->
                                   a >= 0 && (a /= 0 || b > 0) && abs b <= 10 && isIntegral b
    wd (FloatBinopE Root x y)    = check2 x y $ \a b -> a >= 0 && b >= 0.1
    wd (FloatBinopE LogBase x y) = check2 x y $ \a b -> a >= 2 && b > 0
    wd _                         = True

    check :: Exp Double -> (Double -> Bool) -> Bool
    check x p = case eval x of
                  ConstE c -> let a = fromConst c
                              in not (isNaN a || isInfinite a) && p a
                  _        -> False

    check2 x y p = check x $ \a -> check y (p a)

    -- 'check' rejects nonfinite values before this conversion.
    isIntegral x = snd (properFraction x :: (Integer, Double)) == 0

    wellScaled x = abs x <= 1e20 && (x == 0 || abs x >= 1e-2)

-- | Generate an arbitrary exact constant.
arbitraryConst :: (Floating a, Arbitrary a) => Gen (Const a)
arbitraryConst = frequency [ (20, Const <$> arbitrary)
                           , (3,  Pi <$> arbitrary)
                           , (3,  pure E)
                           , (20, IntegerC <$> arbitrary)
                           , (20, RationalC <$> arbitrary)
                           ]

-- | Generate an arbitrary exact constant
arbitraryExactConst :: Fractional a => Gen (Const a)
arbitraryExactConst = oneof [ IntegerC <$> arbitrary
                            , RationalC <$> arbitrary
                            ]

arbitraryClosedExp :: forall a . (Ord a, Floating a, Floating (Const a), IsConst a)
                   => (Exp a -> Bool)
                   -> Gen (Exp a)
arbitraryClosedExp wd = sized $ \n ->
    frequency [ (1, ConstE <$> arbitraryExactConst)
              , (if n > 1 then 1 else 0, discardNotWellDefined =<<
                                         NumUnopE <$> arbitraryBoundedEnum
                                                  <*> resize (n - 1) arb)
              , (if n > 1 then 1 else 0, discardNotWellDefined =<<
                                         FracUnopE <$> arbitraryBoundedEnum
                                                   <*> resize (n - 1) arb)
              , (if n > 1 then 1 else 0, discardNotWellDefined =<<
                                         FloatUnopE <$> arbitraryBoundedEnum
                                                    <*> resize (n - 1) arb)
              , (if n > 2 then 1 else 0, discardNotWellDefined =<<
                                         NumBinopE <$> arbitraryBoundedEnum
                                                   <*> resize (n `div` 2) arb
                                                   <*> resize (n `div` 2) arb)
              , (if n > 2 then 1 else 0, discardNotWellDefined =<<
                                         IntPowE <$> resize (n `div` 2) arb
                                                 <*> (getPositive <$> resize (n `div` 2) arbitrary))
              , (if n > 2 then 1 else 0, discardNotWellDefined =<<
                                         FracPowE <$> resize (n `div` 2) arb
                                                  <*> resize (n `div` 2) arbitrary)
              , (if n > 2 then 1 else 0, discardNotWellDefined =<<
                                         FracBinopE <$> arbitraryBoundedEnum
                                                    <*> resize (n `div` 2) arb
                                                    <*> resize (n `div` 2) arb)
              , (if n > 2 then 1 else 0, discardNotWellDefined =<<
                                         FloatBinopE <$> arbitraryBoundedEnum
                                                     <*> resize (n `div` 2) arb
                                                     <*> resize (n `div` 2) arb)
              ]
  where
    arb :: Gen (Exp a)
    arb = arbitraryClosedExp wd

    discardNotWellDefined :: Exp a -> Gen (Exp a)
    discardNotWellDefined e | wd e      = pure e
                            | otherwise = pure discard

shrinkExp :: (Exp Double -> Bool)
          -> Exp Double
          -> [Exp Double]
shrinkExp wd = shrinkOne
  where
    shrinkOne :: Exp Double -> [Exp Double]
    shrinkOne (NumUnopE op e)        = filter wd $
                                    pure e
                                    <|> NumUnopE op <$> evalshrink e
                                    <|> NumUnopE op <$> shrinkOne e
    shrinkOne (FracUnopE op e)       = filter wd $
                                    pure e
                                    <|> FracUnopE op <$> evalshrink e
                                    <|> FracUnopE op <$> shrinkOne e
    shrinkOne (FloatUnopE op e)      = filter wd $
                                    pure e
                                    <|> FloatUnopE op <$> evalshrink e
                                    <|> FloatUnopE op <$> shrinkOne e
    shrinkOne (NumBinopE op e1 e2)   = filter wd $
                                    pure e1 <|> pure e2
                                    <|> NumBinopE op <$> evalshrink e1 <*> pure e2
                                    <|> NumBinopE op e1 <$> evalshrink e2
                                    <|> NumBinopE op <$> shrinkOne e1 <*> pure e2
                                    <|> NumBinopE op e1 <$> shrinkOne e2
    shrinkOne (IntPowE e n)          = filter wd $
                                    pure e <|> pure (fromInteger n)
                                    <|> IntPowE <$> evalshrink e <*> pure n
                                    <|> IntPowE <$> shrinkOne e <*> pure n
                                    <|> if n > 0 then pure (IntPowE e (n-1)) else empty
    shrinkOne (FracPowE e n)         = filter wd $
                                    pure e <|> pure (fromInteger n)
                                    <|> FracPowE <$> evalshrink e <*> pure n
                                    <|> FracPowE <$> shrinkOne e <*> pure n
                                    <|> if n > 0 then pure (FracPowE e (n-1)) else empty
    shrinkOne (IntBinopE op e1 e2)   = filter wd $
                                    pure e1 <|> pure e2
                                    <|> IntBinopE op <$> evalshrink e1 <*> pure e2
                                    <|> IntBinopE op e1 <$> evalshrink e2
                                    <|> IntBinopE op <$> shrinkOne e1 <*> pure e2
                                    <|> IntBinopE op e1 <$> shrinkOne e2
    shrinkOne (FracBinopE op e1 e2)  = filter wd $
                                    pure e1 <|> pure e2
                                    <|> FracBinopE op <$> evalshrink e1 <*> pure e2
                                    <|> FracBinopE op e1 <$> evalshrink e2
                                    <|> FracBinopE op <$> shrinkOne e1 <*> pure e2
                                    <|> FracBinopE op e1 <$> shrinkOne e2
    shrinkOne (FloatBinopE op e1 e2) = filter wd $
                                    pure e1 <|> pure e2
                                    <|> FloatBinopE op <$> evalshrink e1 <*> pure e2
                                    <|> FloatBinopE op e1 <$> evalshrink e2
                                    <|> FloatBinopE op <$> shrinkOne e1 <*> pure e2
                                    <|> FloatBinopE op e1 <$> shrinkOne e2
    shrinkOne _                      = empty

    evalshrink :: Alternative f => Exp Double -> f (Exp Double)
    evalshrink _ = empty

newtype DExp = DExp (Exp Double)
  deriving (Eq, Ord, Show, Num, Fractional, Floating)

instance Arbitrary DExp where
    arbitrary = DExp <$> arbitraryClosedExp wellDefined

    shrink (DExp e) = map DExp (shrinkExp wellDefined e)

newtype ExactDExp = ExactDExp (Exp Double)
  deriving (Eq, Ord, Show, Num, Fractional, Floating)

wellDefinedExact :: Exp Double -> Bool
wellDefinedExact FloatUnopE{}  = False
wellDefinedExact FloatBinopE{} = False
wellDefinedExact e             = wellDefined e

instance Arbitrary ExactDExp where
    arbitrary = ExactDExp <$> arbitraryClosedExp wellDefinedExact

    shrink (ExactDExp e) = map ExactDExp (shrinkExp wellDefinedExact e)

evalTests :: Spec
evalTests = describe "Evaluation" $ do
    describe "Numeric test helpers" $ do
      forM_ [("sine", FloatUnopE Sin 1),
             ("cosine", FloatUnopE Cos 1),
             ("negative pi", ConstE (Pi (-1))),
             ("integer power", FloatBinopE Pow 2 3),
             ("evaluated integer exponent", FloatBinopE Pow 2 (ConstE (Const 3))),
             ("negative exponent", FloatBinopE Pow 4 (-2))] $ \(name, e) ->
        it ("admits finite " ++ name ++ " values") $
          wellDefined (e :: Exp Double) @?= True
      forM_ [("negative square root", FloatUnopE Sqrt (ConstE (Pi (-1)))),
             ("negative logarithm", FloatUnopE Log (ConstE (Pi (-1)))),
             ("zero reciprocal", FracUnopE Recip 0),
             ("positive atanh endpoint", FloatUnopE Atanh 1),
             ("negative atanh endpoint", FloatUnopE Atanh (-1)),
             ("overflow", FloatUnopE Exp 1000),
             ("inexact overflow", ConstE (IntegerC (10^(400 :: Integer)))),
             ("undefined value", Undefined),
             ("open expression", VarE "x")] $ \(name, e) ->
        it ("rejects " ++ name) $
          wellDefined (e :: Exp Double) @?= False
      forM_ [("NaN", 0/0), ("positive infinity", 1/0), ("negative infinity", -1/0)] $ \(name, payload) ->
        it ("rejects a " ++ name ++ " payload") $
          wellDefined (ConstE (Const payload) :: Exp Double) @?= False
    it "Exact evaluation evaluates all exact expressions" $
      property prop_eval_evalexact_equiv

prop_eval_evalexact_equiv :: ExactDExp -> Property
prop_eval_evalexact_equiv (ExactDExp e) = evalexact e === eval e
