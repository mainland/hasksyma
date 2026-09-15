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
import           Data.Complex        (Complex (..))
import           Data.Ratio          (denominator)
import           Test.Hspec          (Spec, describe, it)
import           Test.HUnit          (assertFailure, (@?=))
import           Test.QuickCheck     (Arbitrary (..), Gen, Positive (..), Property,
                                      Testable (property), arbitraryBoundedEnum, discard, frequency,
                                      oneof, resize, sized, (===), (==>))

import           Hasksyma.Const      (Const (..), IsConst (fromConst, samePayload))
import           Hasksyma.Eval       (eval, evalexact)
import           Hasksyma.Exp        (Exp (..), FloatBinop (..), FloatUnop (..), FracBinop (..),
                                      FracUnop (..), NumBinop (..), NumUnop (..), isExactE, sameExp)

-- | Select finite, well-scaled closed expressions for numerical properties.
-- The ranges deliberately sample less than the full mathematical domains.
-- Compare numerical values, since expression ordering only orders syntax.
wellDefined :: Exp Double -> Bool
wellDefined e = wd e && check e wellScaled
  where
    wd (NumUnopE Signum x)       = check x (>= 0.1)
    wd (NatPowE _ n)             = n > 0 && n <= 10
    wd (IntPowE x n)             = check x $ \a -> abs n <= 10 && (a /= 0 || n > 0)
    wd (FracPowE x q)            = check x $ \a -> a >= 0 && abs q <= 10 && (a /= 0 || q > 0)
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
                                         NatPowE <$> resize (n `div` 2) arb
                                                 <*> (fromInteger . getPositive <$> resize (n `div` 2) arbitrary))
              , (if n > 2 then 1 else 0, discardNotWellDefined =<<
                                         IntPowE <$> resize (n `div` 2) arb
                                                  <*> resize (n `div` 2) arbitrary)
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
    shrinkOne (NatPowE e n)          = filter wd $
                                    pure e <|> pure (fromIntegral n)
                                    <|> NatPowE <$> evalshrink e <*> pure n
                                    <|> NatPowE <$> shrinkOne e <*> pure n
                                    <|> if n > 0 then pure (NatPowE e (fromInteger (toInteger n-1))) else empty
    shrinkOne (IntPowE e n)          = filter wd $
                                    pure e <|> pure (fromInteger n)
                                    <|> IntPowE <$> evalshrink e <*> pure n
                                    <|> IntPowE <$> shrinkOne e <*> pure n
                                    <|> if n > 0 then pure (IntPowE e (n-1)) else empty
    shrinkOne (FracPowE e n)         = filter wd $
                                    pure e <|> pure (fromRational n)
                                    <|> FracPowE <$> evalshrink e <*> pure n
                                    <|> FracPowE <$> shrinkOne e <*> pure n
                                    <|> FracPowE e <$> shrink n
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
wellDefinedExact FracPowE{}    = False
wellDefinedExact e             = wellDefined e

instance Arbitrary ExactDExp where
    arbitrary = ExactDExp <$> arbitraryClosedExp wellDefinedExact

    shrink (ExactDExp e) = map ExactDExp (shrinkExp wellDefinedExact e)

evalTests :: Spec
evalTests = describe "Evaluation" $ do
    describe "Zero division" $ do
      forM_ [("positive quotient", FracBinopE FDiv 1 0, 1/0),
             ("negative quotient", FracBinopE FDiv (ConstE (IntegerC (-1))) 0, -1/0),
             ("zero quotient", FracBinopE FDiv 0 0, 0/0),
             ("reciprocal", FracUnopE Recip 0, 1/0),
             ("negative power", IntPowE 0 (-2), 1/0)] $ \(name, e, expected) -> do
        it ("evaluates a " ++ name ++ " using Double semantics") $
          case eval e :: Exp Double of
            ConstE (Const value) -> samePayload value expected @?= True
            result               -> assertFailure $ show result
        it ("leaves a " ++ name ++ " unreduced during exact evaluation") $
          sameExp (evalexact e) e @?= True
      it "evaluates division by a computed zero denominator" $
        case eval (FracBinopE FDiv 1 (NumBinopE Sub 2 2) :: Exp Double) of
          ConstE (Const value) -> value @?= 1/0
          result               -> assertFailure $ show result
      it "evaluates an overloaded division expression" $
        case eval (1/0 :: Exp Double) of
          ConstE (Const value) -> value @?= 1/0
          result               -> assertFailure $ show result
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

    it "Evaluation preserves signed powers of symbolic bases" $
      property $ \n -> eval (IntPowE x n) === IntPowE x n
    it "Exact evaluation preserves signed powers of symbolic bases" $
      property $ \n -> evalexact (IntPowE x n) === IntPowE x n
    it "Evaluation computes negative powers of constants" $
      eval (IntPowE (ConstE (IntegerC 2)) (-3) :: Exp Rational) @?= ConstE (RationalC (1 / 8))
    it "Exact evaluation computes negative powers of constants" $ do
      let result = evalexact (IntPowE (ConstE (IntegerC 2)) (-3) :: Exp Rational)
      result @?= ConstE (RationalC (1 / 8))
      isExactE result @?= True
    it "Evaluation preserves natural powers of symbolic bases" $
      property $ \(Positive n) ->
        eval (NatPowE x (fromInteger n)) === NatPowE x (fromInteger n)
    it "Exact evaluation preserves natural powers of symbolic bases" $
      property $ \(Positive n) ->
        evalexact (NatPowE x (fromInteger n)) === NatPowE x (fromInteger n)
    it "Evaluation computes a zero natural power" $
      eval (NatPowE (ConstE (IntegerC 2)) 0 :: Exp Integer) @?= 1
    it "Exact evaluation computes a zero natural power" $
      evalexact (NatPowE (ConstE (IntegerC 2)) 0 :: Exp Integer) @?= 1
    it "Evaluation preserves rational powers of symbolic bases" $
      property $ \n -> eval (FracPowE y n) === FracPowE y n
    it "Exact evaluation preserves rational powers of symbolic bases" $
      property $ \n -> denominator n /= 1 ==> evalexact (FracPowE y n) === FracPowE y n
    it "Exact evaluation normalizes integral rational exponents" $
      evalexact (FracPowE y (-2)) @?= IntPowE y (-2)
    it "Evaluation computes rational powers of constants" $
      eval (FracPowE (ConstE (IntegerC 4)) (1 / 2) :: Exp Double) @?= 2
    it "Exact evaluation preserves rational powers requiring approximation" $
      evalexact (FracPowE (ConstE (IntegerC 2)) (1 / 2) :: Exp Double) @?=
        FracPowE (ConstE (IntegerC 2)) (1 / 2)
    it "Rational powers retain the real floating-power semantics for negative bases" $ do
      let base = ConstE (IntegerC (-8)) :: Exp Double
      isNaNConstant (eval (FracPowE base (1 / 3))) @?= True
      isNaNConstant (eval (FloatBinopE Pow base (ConstE (RationalC (1 / 3))))) @?= True
    it "Rational powers agree with general floating powers for complex bases" $
      let base = ConstE (Const ((-1) :+ 0)) :: Exp (Complex Double)
      in eval (FracPowE base (1 / 2)) @?=
           eval (FloatBinopE Pow base (ConstE (RationalC (1 / 2))))
  where
    x :: Exp Rational
    x = VarE "x"

    y :: Exp Double
    y = VarE "y"

    isNaNConstant :: Exp Double -> Bool
    isNaNConstant (ConstE value) = isNaN (fromConst value)
    isNaNConstant _              = False

prop_eval_evalexact_equiv :: ExactDExp -> Property
prop_eval_evalexact_equiv (ExactDExp e) = evalexact e === eval e
