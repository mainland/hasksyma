{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

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

import Control.Applicative ( Alternative, (<|>), empty )
import Control.Monad ( when )
import Test.Hspec ( describe, it, Spec )
import Test.QuickCheck
    ( Arbitrary(..),
      arbitraryBoundedEnum,
      discard,
      frequency,
      oneof,
      resize,
      sized,
      (===),
      Gen,
      Positive(getPositive),
      Property,
      Testable(property) )

import Hasksyma.Const ( Const(..), IsConst(fromConst) )
import Hasksyma.Eval ( eval, evalexact )
import Hasksyma.Exp
    ( Exp(..),
      FloatUnop(..),
      FloatBinop(..),
      FracBinop(..),
      FracUnop(..),
      NumUnop(..) )

-- | Return 'True' if expression is an integral constant.
isIntegral :: Exp a -> Bool
isIntegral (ConstE IntegerC{}) = True
isIntegral _                   = False

-- | Return 'True' if expression is well-defined.
wellDefined :: (Ord a, IsConst a, Fractional a) => Exp a -> Bool
wellDefined = wd
  where
    wd (NumUnopE Signum e) | eval e < 0.1 = False

    wd e@(IntPowE e1 y) | y <= 0 || abs y > 10 = False
      where
        x = eval e1

    wd e@(FracPowE e1 y) | (x == 0 && y <= 0) || abs y > 10 = False
      where
        x = eval e1

    wd (FracUnopE Recip e) | eval e == 0 = False

    wd (FloatUnopE Log e) | eval e < 0.1 = False

    wd (FloatUnopE Exp e) | eval e < 0.1 = False

    wd (FloatUnopE Sqrt e) | eval e < 0 = False

    wd (FloatUnopE Sin e) | x < -pi || x > pi = False
      where
        x = eval e

    wd (FloatUnopE Cos e) | x < -pi || x > pi = False
      where
        x = eval e

    wd (FloatUnopE Tan e) | x < -pi/2 || x > pi/2 = False
      where
        x = eval e

    wd (FloatUnopE Asin e) | x < -1 || x > 1 = False
      where
        x = eval e

    wd (FloatUnopE Acos e) | x < -1 || x > 1 = False
      where
        x = eval e

    wd (FloatUnopE Sinh e) | x < -10 || x > 10 = False
      where
        x = eval e

    wd (FloatUnopE Cosh e) | x < -10 || x > 10 = False
      where
        x = eval e

    wd (FloatUnopE Acosh e) | eval e < 1 = False

    wd (FloatUnopE Atanh e) | x < -1 || x > 1 = False
      where
        x = eval e

    wd (FracBinopE FDiv _ e2) | eval e2 == 0 = False

    wd e@(FloatBinopE Pow e1 e2) | (x == 0 && y <= 0) || (x < 0 || not (isIntegral y))|| abs y > 10 = False
      where
        x = eval e1
        y = eval e2

    wd (FloatBinopE Root e1 e2) | x < 0 || y <= 0 || abs y < (1/10) = False
      where
        x = eval e1
        y = eval e2

    wd (FloatBinopE LogBase e1 e2) | eval e1 < 2 || eval e2 <= 0 = False

    wd e = not (illSized e)

    -- | Determine if an expression is ill-sized
    illSized :: (Ord a, Fractional a, IsConst a) => Exp a -> Bool
    illSized e = case eval e of
                   ConstE c -> let x = fromConst c
                               in
                                  abs x > 1e20 || (x /= 0 && abs x < 1e-2)
                   _        -> False

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
shrinkExp wd = shrink
  where
    shrink :: Exp Double -> [Exp Double]
    shrink (NumUnopE op e)        = filter wd $
                                    pure e
                                    <|> NumUnopE op <$> evalshrink e
                                    <|> NumUnopE op <$> shrink e
    shrink (FracUnopE op e)       = filter wd $
                                    pure e
                                    <|> FracUnopE op <$> evalshrink e
                                    <|> FracUnopE op <$> shrink e
    shrink (FloatUnopE op e)      = filter wd $
                                    pure e
                                    <|> FloatUnopE op <$> evalshrink e
                                    <|> FloatUnopE op <$> shrink e
    shrink (NumBinopE op e1 e2)   = filter wd $
                                    pure e1 <|> pure e2
                                    <|> NumBinopE op <$> evalshrink e1 <*> pure e2
                                    <|> NumBinopE op e1 <$> evalshrink e2
                                    <|> NumBinopE op <$> shrink e1 <*> pure e2
                                    <|> NumBinopE op e1 <$> shrink e2
    shrink (IntPowE e n)          = filter wd $
                                    pure e <|> pure (fromInteger n)
                                    <|> IntPowE <$> evalshrink e <*> pure n
                                    <|> IntPowE <$> shrink e <*> pure n
                                    <|> if n > 0 then pure (IntPowE e (n-1)) else empty
    shrink (FracPowE e n)         = filter wd $
                                    pure e <|> pure (fromInteger n)
                                    <|> FracPowE <$> evalshrink e <*> pure n
                                    <|> FracPowE <$> shrink e <*> pure n
                                    <|> if n > 0 then pure (FracPowE e (n-1)) else empty
    shrink (IntBinopE op e1 e2)   = filter wd $
                                    pure e1 <|> pure e2
                                    <|> IntBinopE op <$> evalshrink e1 <*> pure e2
                                    <|> IntBinopE op e1 <$> evalshrink e2
                                    <|> IntBinopE op <$> shrink e1 <*> pure e2
                                    <|> IntBinopE op e1 <$> shrink e2
    shrink (FracBinopE op e1 e2)  = filter wd $
                                    pure e1 <|> pure e2
                                    <|> FracBinopE op <$> evalshrink e1 <*> pure e2
                                    <|> FracBinopE op e1 <$> evalshrink e2
                                    <|> FracBinopE op <$> shrink e1 <*> pure e2
                                    <|> FracBinopE op e1 <$> shrink e2
    shrink (FloatBinopE op e1 e2) = filter wd $
                                    pure e1 <|> pure e2
                                    <|> FloatBinopE op <$> evalshrink e1 <*> pure e2
                                    <|> FloatBinopE op e1 <$> evalshrink e2
                                    <|> FloatBinopE op <$> shrink e1 <*> pure e2
                                    <|> FloatBinopE op e1 <$> shrink e2
    shrink _                      = empty

    evalshrink :: Alternative f => Exp Double -> f (Exp Double)
    evalshrink e = empty

newtype DExp = DExp (Exp Double)
  deriving (Eq, Ord, Show, Num, Fractional, Floating)

instance Arbitrary DExp where
    arbitrary = DExp <$> arbitraryClosedExp wellDefined

    shrink (DExp e) = map DExp (shrinkExp wellDefined e)

newtype ExactDExp = ExactDExp (Exp Double)
  deriving (Eq, Ord, Show, Num, Fractional, Floating)

wellDefinedExact :: (Ord a, IsConst a, Fractional a) => Exp a -> Bool
wellDefinedExact FloatUnopE{}  = False
wellDefinedExact FloatBinopE{} = False
wellDefinedExact e             = wellDefined e

instance Arbitrary ExactDExp where
    arbitrary = ExactDExp <$> arbitraryClosedExp wellDefinedExact

    shrink (ExactDExp e) = map ExactDExp (shrinkExp wellDefinedExact e)

evalTests :: Spec
evalTests = describe "Evaluation" $ do
    it "Exact evaluation evaluates all exact expressions" $
      property prop_eval_evalexact_equiv

prop_eval_evalexact_equiv :: ExactDExp -> Property
prop_eval_evalexact_equiv (ExactDExp e) = evalexact e === eval e
