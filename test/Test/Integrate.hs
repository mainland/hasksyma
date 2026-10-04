{-# LANGUAGE CPP               #-}
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
import qualified Data.Set           as Set
import           Test.Hspec         (Spec, describe, it)
import           Test.HUnit         (Assertion, assertBool, assertFailure, (@?=))

import           Hasksyma.Const
import           Hasksyma.Diff      (diff)
import           Hasksyma.Eval      (eval)
import           Hasksyma.Exp       (Exp (..), FloatBinop (..), FloatUnop (Tan), FracBinop (..),
                                     FracUnop (..), NumBinop (..), isExactE, sameExp)
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
  integralDependencyTests
  tangentIntegralTests
  logarithmicIntegralTests
  factorizationRegressionTests
  describe "Factorization" $ do
    describe "Factor division" $ do
      it "retains denominator factors when the numerator represents one" $
        divideFactors [] [(x, 1)] @?= [(x, -1 :: Const Double)]
      it "retains every factor of an inverse product" $
        divideFactors [] [(x, 2), (y, 3)] @?= [(x, -2 :: Const Double), (y, -3)]
      it "combines repeated denominator factors" $
        divideFactors [] [(x, 1), (x, 2)] @?= [(x, -3 :: Const Double)]
      it "inverts negative denominator exponents" $
        divideFactors [] [(x, -2)] @?= [(x, 2 :: Const Double)]
      it "removes zero exponents without dropping other denominator factors" $
        divideFactors [] [(x, 0), (y, 2)] @?= [(y, -2 :: Const Double)]
      it "preserves exact rational exponents" $
        case divideFactors [] [(x, RationalC (1/2) :: Const Double)] of
          [(base, power)] -> do
            base @?= x
            sameConst power (RationalC (-1/2)) @?= True
          result -> assertFailure $ show result
      it "continues through the denominator after cancelling a numerator factor" $
        divideFactors [(x, 2)] [(x, 2), (y, 1)] @?= [(y, -1 :: Const Double)]
      it "preserves a numerator divided by one" $
        divideFactors [(x, 2)] [] @?= [(x, 2 :: Const Double)]
      it "returns the empty factorization for one divided by one" $
        (divideFactors [] [] :: [(Exp Double, Const Double)]) @?= []
      it "reconstructs the value of an inverse constant power" $
        case eval (unfactorize (divideFactors [] [(2, 3)]) :: Exp Double) of
          ConstE c -> fromConst c @?= 1/8
          result   -> assertFailure $ show result
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
        assertIntegral (power x (-1)) (log (NatPowE x 2) / 2)
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
    it "int 1/x dx = log(x^2)/2" $
      integrate (integral (1 / x) x :: Exp Double) @?= log (NatPowE x 2) / 2
  where
    half :: Const Double
    half = RationalC (1 / 2)

    x :: Exp a
    x = VarE "x"

    y :: Exp a
    y = VarE "y"

logarithmicIntegralTests :: Spec
logarithmicIntegralTests = describe "Logarithmic integration" $ do
    forM_ integrands $ \(name, integrand) ->
      it ("integrates " ++ name ++ " on positive and negative real intervals") $
        case heuristicIntegrate integrand "x" :: Maybe (Exp Double) of
          Just antideriv -> do
            let derivative = simplify (diff antideriv x)
            forM_ [-3, -2, -0.5, 0.5, 2, 3] $ \point -> do
              let actual = valueAt point antideriv
                  expected = valueAt point integrand
                  h = 1e-5
                  slope = (valueAt (point+h) antideriv - valueAt (point-h) antideriv) / (2*h)
              assertBool (show actual) (not (isNaN actual || isInfinite actual))
              assertBool (show derivative) (abs (valueAt point derivative - expected) < 1e-12)
              assertBool (show slope) (abs (slope - expected) < 1e-8)
          Nothing -> assertFailure "No logarithmic antiderivative"
    it "agrees with log(abs x) for nonzero real arguments" $
      case heuristicIntegrate (1/x) "x" :: Maybe (Exp Double) of
        Just antideriv -> forM_ [-3, -0.5, 0.5, 3] $ \point ->
          assertBool (show point) (abs (valueAt point antideriv - log (abs point)) < 1e-12)
        Nothing -> assertFailure "No logarithmic antiderivative"
    it "keeps the zero singularity of a reciprocal integral" $
      case heuristicIntegrate (1/x) "x" :: Maybe (Exp Double) of
        Just antideriv -> assertBool (show antideriv) (isInfinite (valueAt 0 antideriv))
        Nothing        -> assertFailure "No logarithmic antiderivative"
    it "uses a squared-logarithm formula with a local complex derivative" $ do
      let z = VarE "z" :: Exp (Complex Double)
          primitive = log (NatPowE z 2) / 2
          derivative = simplify (diff primitive z)
      forM_ [1 :+ 0.5, (-1) :+ 0.5, (-1) :+ (-0.5)] $ \point -> do
        assertBool (show point) (magnitude (valueAt point derivative - recip point) < 1e-12)
        forM_ [1e-5 :+ 0, 0 :+ 1e-5] $ \h -> do
          let slope = (valueAt (point+h) primitive - valueAt (point-h) primitive) / (2*h)
          assertBool (show slope) (magnitude (slope - recip point) < 1e-8)
  where
    x :: Exp Double
    x = VarE "x"

    integrands :: [(String, Exp Double)]
    integrands =
      [ ("a quotient", 1/x)
      , ("an overloaded reciprocal", recip x)
      , ("a raw reciprocal", FracUnopE Recip x)
      , ("a normalized reciprocal", simplify (recip x))
      , ("a negative integer power", IntPowE x (-1))
      , ("a linear substitution", 1/(2*x+1/2))
      , ("a quadratic substitution", x/(NatPowE x 2-1))
      ] ++ [(name, power x (-1)) | (name, power) <- realPowerForms]

    valueAt :: (Eq a, Num a, IsConst a) => a -> Exp a -> a
    valueAt point e = case eval (mapExp replace e) of
                       ConstE c -> fromConst c
                       _        -> error "Expected a constant after evaluation"
      where
        replace VarE{} = ConstE (Const point)
        replace other  = other

tangentIntegralTests :: Spec
tangentIntegralTests = describe "Tangent integration" $ do
    it "returns real values on intervals with either sign of cosine" $
      withPrimitive $ \primitive ->
        forM_ realPoints $ \point ->
          assertClose (-log (abs (cos point))) (valueAt point (primitive x))
    it "differentiates to tangent on both real domains" $
      withPrimitive $ \primitive ->
        forM_ realPoints $ \point ->
          assertClose (tan point) (valueAt point (simplify (diff (primitive x) x)))
    it "has the correct numerical slope where real cosine is negative" $
      withPrimitive $ \primitive ->
        forM_ [-3, -2, 2, 3] $ \point ->
          let h = 1e-5
              slope = (valueAt (point+h) (primitive x) - valueAt (point-h) (primitive x)) / (2*h)
          in assertBool (show slope) (abs (slope - tan point) < 1e-8)
    it "supports heuristic integration and linear substitution across real intervals" $
      forM_ [tan x, tan (2*x+1)] $ \integrand ->
        case heuristicIntegrate integrand "x" :: Maybe (Exp Double) of
          Just antideriv -> forM_ realPoints $ \point -> do
            let value = valueAt point antideriv
            assertBool (show value) (not (isNaN value || isInfinite value))
            assertClose (valueAt point integrand) (valueAt point (simplify (diff antideriv x)))
          Nothing -> assertFailure "No tangent antiderivative"
    it "retains a local complex antiderivative away from logarithm cuts" $
      case tableIntegrate Tan :: Maybe (Exp (Complex Double) -> Exp (Complex Double)) of
        Just primitive -> do
          let z = VarE "z"
              derivative = simplify (diff (primitive z) z)
          forM_ [0.5 :+ 0.25, 2 :+ 0.25, (-2) :+ (-0.5)] $ \point -> do
            assertBool (show point) (magnitude (valueAt point derivative - tan point) < 1e-12)
            forM_ [1e-5 :+ 0, 0 :+ 1e-5] $ \h -> do
              let slope = (valueAt (point+h) (primitive z) - valueAt (point-h) (primitive z)) / (2*h)
              assertBool (show slope) (magnitude (slope - tan point) < 1e-8)
        Nothing -> assertFailure "No complex tangent antiderivative"
  where
    x :: Exp Double
    x = VarE "x"

    realPoints :: [Double]
    realPoints = [-3, -2, -0.5, 0, 0.5, 2, 3, 7]

    withPrimitive :: ((Exp Double -> Exp Double) -> Assertion) -> Assertion
    withPrimitive action = case tableIntegrate Tan of
                             Just primitive -> action primitive
                             Nothing        -> assertFailure "No tangent antiderivative"

    valueAt :: (Eq a, Num a, IsConst a) => a -> Exp a -> a
    valueAt point e = case eval (mapExp replace e) of
                       ConstE c -> fromConst c
                       _        -> error "Expected a constant after evaluation"
      where
        replace VarE{} = ConstE (Const point)
        replace other  = other

    assertClose :: Double -> Double -> Assertion
    assertClose expected actual =
      assertBool (show actual ++ ", expected " ++ show expected) $
        abs (actual - expected) < 1e-12 * max 1 (abs expected)

integralDependencyTests :: Spec
integralDependencyTests = describe "Integral dependencies" $ do
    forM_ [("binds the definite integration variable", definite, []),
           ("retains free integrand parameters", IntE (Just (0, 1)) (NumBinopE Mul x y) "x", ["y"]),
           ("retains free variables from both bounds", IntE (Just (y, z)) x "x", ["y", "z"]),
           ("does not bind its variable in the lower bound", IntE (Just (x, 1)) x "x", ["x"]),
           ("does not bind its variable in the upper bound", IntE (Just (0, x)) x "x", ["x"]),
           ("retains the variable of a constant antiderivative", antiderivative, ["x"]),
           ("retains antiderivative parameters", IntE Nothing y "x", ["x", "y"]),
           ("conservatively retains the variable of a zero antiderivative", IntE Nothing 0 "x", ["x"]),
           ("binds dependencies introduced by a nested antiderivative", IntE (Just (0, 1)) antiderivative "x", []),
           ("retains the outer variable around a closed definite integral", IntE Nothing definite "x", ["x"]),
           ("respects nested definite integrals with the same variable", IntE (Just (0, 1)) (IntE (Just (0, x)) x "x") "x", []),
           ("retains antiderivative dependencies under differentiation", DiffE antiderivative "x", ["x"])] $
      \(name, e, expected) -> it name $ fvs e @?= Set.fromList expected
    it "does not treat an antiderivative as a constant when integrating it again" $ do
      freeOf "x" antiderivative @?= False
      (heuristicIntegrate antiderivative "x" :: Maybe (Exp Double)) @?= Nothing
    it "recognizes a closed definite integral as a constant factor" $ do
      freeOf "x" definite @?= True
      (heuristicIntegrate definite "x" :: Maybe (Exp Double)) @?= Just (definite * x)
    it "does not treat a definite integral with a variable bound as constant" $
      freeOf "x" (IntE (Just (0, x)) x "x") @?= False
    it "still integrates nested constant integrals after reducing the inner integral" $
      simplify (integrate (IntE Nothing antiderivative "x")) @?=
        simplify (FracBinopE FDiv (NatPowE x 2) 2)
  where
    x, y, z :: Exp Double
    x = VarE "x"
    y = VarE "y"
    z = VarE "z"

    definite = IntE (Just (0, 1)) x "x"
    antiderivative = IntE Nothing 1 "x"

realPowerForms :: [(String, Exp Double -> Rational -> Exp Double)]
realPowerForms =
  [ ("Rational powers", FracPowE)
  , ("General powers with rational constants", \e q -> FloatBinopE Pow e (ConstE (RationalC q)))
  , ("General powers with evaluated constants", \e q -> FloatBinopE Pow e (ConstE (Const (fromRational q))))
  ]

assertIntegral :: Exp Double -> Exp Double -> Assertion
assertIntegral integrand expected =
  case heuristicIntegrate integrand "x" of
    Just actual -> do
      let (a, actualFactors) = coefficient (factorize (simplify actual))
          (b, expectedFactors) = coefficient (factorize (simplify expected))
      actualFactors @?= expectedFactors
      -- Compare evaluated coefficients explicitly, since these examples also
      -- include powers with already evaluated exponents.
      assertBool ("Coefficient " ++ show a ++ ", expected " ++ show b) $
        not (isNaN a || isInfinite a || isNaN b || isInfinite b)
        && abs (a - b) <= 1e-12 * max 1 (abs b)
    Nothing     -> assertFailure $ "Failed to integrate " ++ show integrand
  where
    coefficient :: [(Exp Double, Const Double)] -> (Double, [(Exp Double, Const Double)])
    coefficient ((ConstE c, 1) : fs) = (fromConst c, fs)
    coefficient fs                   = (1, fs)

factorizationRegressionTests :: Spec
factorizationRegressionTests = describe "Factorization regressions" $ do
    forM_ constants $ \(name, c) -> describe name $ do
      it "retains the exact constant as a symbolic factor" $
        case factorize (ConstE c) of
          [(base, power)] -> do
            sameExp base (ConstE c) @?= True
            sameConst power (IntegerC 1) @?= True
          result -> assertFailure $ show result
      it "preserves exactness through factorization and reconstruction" $
        forM_ [(ConstE c, fromConst c),
               (NatPowE (ConstE c) 2, fromConst c ^ (2 :: Integer)),
               (IntPowE (ConstE c) (-1), recip (fromConst c)),
               (NumBinopE Mul (ConstE c) (ConstE E), fromConst c * exp 1)] $ \(e, expected) -> do
          let factors = factorize e
          assertBool (show factors) (all (\(base, power) -> isExactE base && isExact power) factors)
          isExactE (unfactorize factors) @?= True
          assertFactorizationValue expected e
      it "retains exact constants in a variable-dependent antiderivative" $
        case heuristicIntegrate (NumBinopE Mul (ConstE c) x) "x" :: Maybe (Exp Double) of
          Just result -> do
            isExactE result @?= True
            assertIntegral (NumBinopE Mul (ConstE c) x) (ConstE c * NatPowE x 2 / 2)
          Nothing -> assertFailure "No antiderivative"
    it "collects rational coefficients without approximation" $ do
      let e = NumBinopE Mul (ConstE (RationalC (2/3))) (IntPowE (ConstE (IntegerC 2)) (-2)) :: Exp Double
      case factorize e of
        [(ConstE c, power)] -> do
          isExact c @?= True
          c @?= RationalC (1/6)
          sameConst power (IntegerC 1) @?= True
        result -> assertFailure $ show result
      isExactE (unfactorize (factorize e)) @?= True
    it "retains a known-zero base with a negative exponent" $
      factorize (IntPowE 0 (-1) :: Exp Double) @?= [(0, -1)]
    it "decomposes raw reciprocals using signed integer exponents" $
      factorize (FracUnopE Recip (NatPowE x 2)) @?= [(x, -2)]
#if defined(CYCLOTOMIC)
    it "preserves exact complex cyclotomic factors" $ do
      let c = sqrt (IntegerC (-1)) :: Const (Complex Double)
          e = NumBinopE Mul (ConstE c) (VarE "z")
      isExactE (unfactorize (factorize e)) @?= True
#endif
  where
    x :: Exp Double
    x = VarE "x"

    constants :: [(String, Const Double)]
    constants = [("Euler's number", E), ("Pi", Pi 1), ("A negative pi multiple", Pi (-2))]
#if defined(CYCLOTOMIC)
                ++ [("An exact real radical", sqrt (IntegerC 2))]
#endif

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
