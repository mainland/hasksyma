{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  Test.Integrate
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Integrate where

import           Control.Monad      (forM_)
import           Data.Complex       (Complex (..), magnitude)
import           Test.Hspec         (Spec, describe, it)
import           Test.HUnit         (Assertion, assertBool, assertFailure, (@?=))

import           Hasksyma.Const
import           Hasksyma.Eval      (eval)
import           Hasksyma.Exp       (Exp (..), FloatBinop (..), FracBinop (..), NumBinop (..))
import           Hasksyma.Integrate
import           Hasksyma.Simplify

integral :: (Show a, Floating a, Floating (Const a)) => Exp a -> Exp a -> Exp a
integral e (VarE x) = IntE Nothing e x
integral _ x        = error $ show x ++ " is not a variable"

integrate :: (Ord a, Floating a, Floating (Const a), IsConst a)
          => Exp a
          -> Exp a
integrate e0 | e1 == e0  = e0
             | otherwise = integrate e1
  where
    e1 = mapExp int1 e0

    int1 (IntE Nothing integrand variable) = case heuristicIntegrate integrand variable of
                                               []            -> IntE Nothing integrand variable
                                               antideriv : _ -> antideriv

    int1 expression = simp expression

integrateTests :: Spec
integrateTests = do
  describe "Factorization" $ do
    it "extracts a positive sign from an even power of a negated factor" $
      factorize ((-x) ^ (2 :: Integer) :: Exp Double) @?= [(x, 2)]
    it "extracts a negative sign from an odd power of a negated factor" $
      factorize ((-x) ^ (3 :: Integer) :: Exp Double) @?=
        [(ConstE (IntegerC (-1)), 1), (x, 3)]
    it "retains a negated base raised to a fractional power" $
      let e = (-x) ** ConstE half :: Exp Double
      in factorize e @?= [(e, 1)]
    it "retains a natural power inside a rational power" $
      let e = FracPowE (NatPowE x 2) (1/2) :: Exp Double
      in factorize e @?= [(e, 1)]
    it "retains a rational power inside a natural power" $
      factorize (NatPowE (FracPowE x (1/2)) 2 :: Exp Double) @?=
        [(FracPowE x (1/2), 2)]
    it "still decomposes general powers with exact integer exponents" $
      factorize (FloatBinopE Pow (NumBinopE Mul x y) (ConstE (IntegerC 2)) :: Exp Double) @?=
        [(x, 2), (y, 2)]
    it "still combines natural and signed integer powers" $
      factorize (NumBinopE Mul (NatPowE x 3) (IntPowE x (-1)) :: Exp Double) @?=
        [(x, 2)]
    it "keeps symbolic exponents inside a factor" $
      let e = FloatBinopE Pow x y :: Exp Double
      in factorize (NatPowE e 2) @?= [(e, 2)]

    forM_ realPowerForms $ \(name, power) -> describe name $ do
      it "keeps the whole fractional power as a factor" $
        let e = power (NumBinopE Mul x y) (1/2)
        in factorize e @?= [(e, 1)]
      it "preserves the root of a product of negative factors" $
        assertFactorizationValue 1 (power (NumBinopE Mul (-1) (-1)) (1/2))
      it "preserves the root of a quotient of negative factors" $
        assertFactorizationValue 2 (power (FracBinopE FDiv (-8) (-2)) (1/2))
      it "preserves a natural power inside a fractional power" $
        assertFactorizationValue 2 (power (NatPowE (-2) 2) (1/2))
      it "preserves a signed power inside a fractional power" $
        assertFactorizationValue 0.5 (power (IntPowE (-2) (-2)) (1/2))
      it "preserves a fractional power inside an integer power" $
        assertFactorizationValue (0/0) (NatPowE (power (-2) (1/2)) 2)
      it "does not merge fractional powers into an integral exponent" $
        assertFactorizationValue (0/0) $
          NumBinopE Mul (power (-8) (1/3)) (power (-8) (2/3))
      it "preserves positive-base products of fractional powers" $
        assertFactorizationValue 8 $
          NumBinopE Mul (power 8 (1/3)) (power 8 (2/3))
      it "preserves zero raised to a positive fractional power" $
        assertFactorizationValue 0 (power 0 (1/2))
      it "preserves zero raised to a negative fractional power" $
        assertFactorizationValue (1/0) (power 0 (-1/2))

    it "preserves complex branches when factoring a fractional power" $ do
      let base = NumBinopE Mul (-1) (-1) :: Exp (Complex Double)
          expressions = [FracPowE base (1/2), FloatBinopE Pow base (ConstE (RationalC (1/2)))]
      forM_ expressions $ \e ->
        forM_ [e, unfactorize (factorize e)] $ \expression ->
          case eval expression of
            ConstE c -> assertBool (show expression) (magnitude (fromConst c - 1) < 1e-12)
            result   -> assertFailure $ "Expected a constant, got " ++ show result

  describe "Integration" $ do
    forM_ realPowerForms $ \(name, power) -> describe name $ do
      it "integrates a fractional power" $
        assertIntegral (power x (1/2)) ((2/3) * power x (3/2))
      it "integrates a negative fractional power" $
        assertIntegral (power x (-1/2)) (2 * power x (1/2))
      it "integrates a fractional power below minus one" $
        assertIntegral (power x (-3/2)) ((-2) * power x (-1/2))
      it "uses the logarithmic rule for an intact power of minus one" $
        assertIntegral (power x (-1)) (log x)
      it "integrates a fractional power of a linear expression" $
        let u = 2*x + 1
        in assertIntegral (power u (1/2)) ((1/3) * power u (3/2))
      it "integrates a fractional power by substitution" $
        let u = NatPowE x 2 + 1
        in assertIntegral (x * power u (1/2)) ((1/3) * power u (3/2))
      it "retains a negated base during substitution" $
        assertIntegral (power (-x) (1/2)) ((-2/3) * power (-x) (3/2))
      it "requires the derivative of the inner expression" $
        (heuristicIntegrate (power (NatPowE x 2 + 1) (1/2)) "x" :: Maybe (Exp Double)) @?= Nothing
      it "does not integrate the square root of a square as the base" $
        (heuristicIntegrate (power (NatPowE x 2) (1/2)) "x" :: Maybe (Exp Double)) @?= Nothing

    it "int x^2 dx = x^3/3" $
        integrate (integral (x^(2 :: Integer)) x :: Exp Double) @?= NatPowE x 3/3
    it "int x * sin(x^2) dx = -1/2*cos (x^2)" $
        integrate (integral (x * sin(x^(2 :: Integer))) x :: Exp Double) @?=
          -(ConstE (RationalC (1/2)) * cos (NatPowE x 2))
  where
    half :: Const Double
    half = RationalC (1 / 2)

    x :: Exp a
    x = VarE "x"

    y :: Exp a
    y = VarE "y"

realPowerForms :: [(String, Exp Double -> Rational -> Exp Double)]
realPowerForms =
  [ ("Rational powers", FracPowE)
  , ("General powers with rational constants", \e q -> FloatBinopE Pow e (ConstE (RationalC q)))
  , ("General powers with evaluated constants", \e q -> FloatBinopE Pow e (ConstE (Const (fromRational q))))
  ]

assertIntegral :: Exp Double -> Exp Double -> Assertion
assertIntegral integrand expected =
  case heuristicIntegrate integrand "x" of
    Just actual -> factorize (simplify actual) @?= factorize (simplify expected)
    Nothing     -> assertFailure $ "Failed to integrate " ++ show integrand

assertFactorizationValue :: Double -> Exp Double -> Assertion
assertFactorizationValue expected e =
  forM_ [e, unfactorize (factorize e)] $ \expression ->
    case eval expression of
      ConstE c ->
        let actual = fromConst c
            matches | isNaN expected = isNaN actual
                    | isInfinite expected = actual == expected
                    | otherwise = not (isNaN actual || isInfinite actual)
                                  && abs (actual - expected) <= 1e-12 * max 1 (abs expected)
        in assertBool (show expression ++ " evaluated to " ++ show actual ++ ", expected " ++ show expected) matches
      result -> assertFailure $ "Expected a constant, got " ++ show result
