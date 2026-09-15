{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  Test.Simplify
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Simplify where

import           Control.Monad                   (forM_)
import           Test.Hspec
import           Test.HUnit
import           Test.QuickCheck
import           Text.PrettyPrint.Mainland       (prettyCompact, text, (<+>))
import           Text.PrettyPrint.Mainland.Class (ppr)

import           Hasksyma.Const
import           Hasksyma.Eval
import           Hasksyma.Exp
import           Hasksyma.Simplify

import           Test.Eval

simplifyTests :: Spec
simplifyTests = describe "Simplification" $ do
    describe "Numeric test helpers" $ do
      forM_ [("zeros", 0, 0), ("equal values", 2, 2),
             ("nearby values", 1, 1 + 1e-13)] $ \(name, x, y) ->
        it ("accepts " ++ name) $
          equiv eps (ConstE (Const x)) (ConstE (Const y))
      it "rejects unequal finite values" $
        expectFailure $ equiv eps 1 2
      forM_ [("NaN", 0/0), ("positive infinity", 1/0), ("negative infinity", -1/0)] $ \(name, x) ->
        forM_ [("left", x, 1), ("right", 1, x), ("both", x, x)] $ \(position, a, b) ->
          it ("rejects " ++ name ++ " in " ++ position ++ " operands") $
            expectFailure $ equiv eps (ConstE (Const a)) (ConstE (Const b))
      forM_ [Undefined, Infty, NegInfty, VarE "x"] $ \e ->
        it ("rejects unevaluated operands: " ++ show e) $
          expectFailure $ equiv eps e e
      forM_ [("zero", 0), ("negative", -1), ("NaN", 0/0), ("infinite", 1/0)] $ \(name, tolerance) ->
        it ("rejects " ++ name ++ " tolerance") $
          expectFailure $ equiv tolerance 0 0
    identityTests
    norvigTests
    prodTests
    powTests
    it "Simplification preserves exactness and evaluation" $
        property $ forAllShrinkBlind arbitrary shrink $ popEvalSimplifyEquiv eps tensec
  where
    eps :: Double
    eps = 1e-12

    tensec :: Int
    tensec = 10 * 1000000

identityTests :: Spec
identityTests = describe "Expression identity" $ do
    it "recognizes unchanged NaN syntax without changing equality" $ do
      let e = FloatUnopE Sin (ConstE (Const (0/0))) :: Exp Double
      sameExp e e @?= True
      (e == e) @?= False
    it "distinguishes equal constant representations inside expressions" $ do
      let a = NumUnopE Neg (ConstE (IntegerC 1)) :: Exp Double
          b = NumUnopE Neg (ConstE (RationalC 1))
      (a == b) @?= True
      sameExp a b @?= False
    it "compares operator and power syntax independently of numeric equality" $ do
      let x = VarE "x" :: Exp Double
      sameExp (NumUnopE Neg x) (NumUnopE Abs x) @?= False
      sameExp (NatPowE x 2) (IntPowE x 2) @?= False
      sameExp (FracPowE x (1/2)) (FracPowE x (1/3)) @?= False
    it "checks calculus variables and both integral bounds around NaNs" $ do
      let nan = ConstE (Const (0/0)) :: Exp Double
          integral l u = IntE (Just (l, u)) nan
      sameExp (integral nan 1 "x") (integral nan 1 "x") @?= True
      sameExp (integral nan 1 "x") (integral nan 2 "x") @?= False
      sameExp (integral 0 nan "x") (integral 1 nan "x") @?= False
      sameExp (integral nan 1 "x") (integral nan 1 "y") @?= False
      sameExp (integral nan 1 "x") (IntE Nothing nan "x") @?= False
      sameExp (IntE Nothing nan "x") (IntE Nothing nan "x") @?= True
      sameExp (IntE Nothing nan "x") (IntE Nothing 1 "x") @?= False
      sameExp (DiffE nan "x") (DiffE nan "y") @?= False

norvigTests :: Spec
norvigTests = do
    describe "Simplification tests from PAIP 8.2" $ do
        it "2 + 2 = 4" $
          simplify (2 + 2 :: Exp Double) @?= 4
        it "5 * 20 + 30 + 7 = 137" $
          simplify (5 * 20 + 30 + 7 :: Exp Double) @?= 137
        it "5 * x - (4 + 1) * x = 0" $
          simplify (5 * x - (4 + 1) * x :: Exp Double) @?= 0
        it "y / z * (5 * z - (4 + 1) * z) = 0" $
          simplify (y / z * (5 * z - (4 + 1) * z) :: Exp Double) @?= 0
        it "(4 - 3) * x + (y / y - 1) * z = x" $
          simplify ((4 - 3) * x + (y / y - 1) * z :: Exp Double) @?= x
    describe "Simplification tests from PAIP 8.3" $ do
        it "3 * 2 * x = 6 * x" $
          simplify (3 * 2 * x :: Exp Double) @?= 6 * x
        it "2 * x * x * 3 = 6 * x^2" $
          simplify (2 * x * x * 3 :: Exp Double) @?= 6 * NatPowE x 2
        it "2 * x * 3 * y * 4 * z * 5 * 6 = 720 * x * y * z" $
          simplify (2 * x * 3 * y * 4 * z * 5 * 6 :: Exp Double) @?= 720 * x * y * z
        it "3 + x + 4 + x = 2*x + 7" $
          simplify (3 + x + 4 + x :: Exp Double) @?= 2*x + 7
        it "2 * x * 3 * x * 4 * (1 / x) * 5 * 6 = 720 * x" $
          simplify (2 * x * 3 * x * 4 * ( 1 / x ) * 5 * 6 :: Exp Double) @?= 720 * x
  where
    x, y, z :: Exp a
    x = VarE "x"
    y = VarE "y"
    z = VarE "z"

prodTests :: SpecWith ()
prodTests =
    describe "product simplification" $ do
        it "x*(y/x) = y" $
          simplify (x*(y/x) :: Exp Double) @?= y
        it "(y/x)*x = y" $
          simplify ((y/x)*x :: Exp Double) @?= y
        it "(x*y)/x = y" $
          simplify ((x*y)/x :: Exp Double) @?= y
        it "(y*x)/x = y" $
          simplify ((y*x)/x :: Exp Double) @?= y
  where
    x, y :: Floating a => Exp a
    x = VarE "x"
    y = VarE "y"

powTests :: SpecWith ()
powTests =
    describe "exp/log/pow simplification" $ do
        it "log (e ** x) = x" $
          simplify (log (e ** x) :: Exp Double) @?= x
        it "e ** log x = x" $
          simplify (e ** log x :: Exp Double) @?= x
        it "(x ** y) * (x ** z) = x ** (y + z)" $
          simplify ((x ** y) * (x ** z) :: Exp Double) @?= x ** (y + z)
        it "(x ** y) / (x ** z) = x ** (y - z)" $
          simplify ((x ** y) / (x ** z) :: Exp Double) @?= x ** (y - z)
        it "recip (x ^ 3) = x ^^ (-3)" $
          simplify (FracUnopE Recip (NatPowE x 3) :: Exp Double) @?= IntPowE x (-3)
        it "x ^ 2 / x ^ 5 = x ^^ (-3)" $
          simplify (FracBinopE FDiv (NatPowE x 2) (NatPowE x 5) :: Exp Double) @?= IntPowE x (-3)
        it "x ^ 5 / x ^ 2 = x ^ 3" $
          simplify (FracBinopE FDiv (NatPowE x 5) (NatPowE x 2) :: Exp Double) @?= NatPowE x 3
        it "(x ^^ (-2)) ^ 3 = x ^^ (-6)" $
          simplify (NatPowE (IntPowE x (-2)) 3 :: Exp Double) @?= IntPowE x (-6)
        it "(x ^ 3) ^^ (-2) = x ^^ (-6)" $
          simplify (IntPowE (NatPowE x 3) (-2) :: Exp Double) @?= IntPowE x (-6)
        it "(x ^^ (-3)) ^^ (-2) = x ^ 6" $
          simplify (IntPowE (IntPowE x (-3)) (-2) :: Exp Double) @?= NatPowE x 6
        it "x ^ 2 * x ^^ (-5) = x ^^ (-3)" $
          simplify (NumBinopE Mul (NatPowE x 2) (IntPowE x (-5)) :: Exp Double) @?= IntPowE x (-3)
        it "x ^^ (-5) * x ^ 2 = x ^^ (-3)" $
          simplify (NumBinopE Mul (IntPowE x (-5)) (NatPowE x 2) :: Exp Double) @?= IntPowE x (-3)
        it "A nonnegative integral rational exponent becomes a natural power" $
          simplify (FracPowE x 3 :: Exp Double) @?= NatPowE x 3
        it "A negative integral rational exponent becomes an integer power" $
          simplify (FracPowE x (-3) :: Exp Double) @?= IntPowE x (-3)
        it "A rational constant exponent becomes a rational power" $
          simplify (FloatBinopE Pow x (ConstE (RationalC (1 / 2))) :: Exp Double) @?= FracPowE x (1 / 2)
        it "Preserves a square followed by a rational square root" $
          simplify (FracPowE (NatPowE x 2) (1 / 2) :: Exp Double) @?=
            FracPowE (NatPowE x 2) (1 / 2)
        it "Preserves a rational square root followed by a square" $
          simplify (NatPowE (FracPowE x (1 / 2)) 2 :: Exp Double) @?=
            NatPowE (FracPowE x (1 / 2)) 2
        it "Does not combine rational powers into an integral power" $
          simplify (NumBinopE Mul (FracPowE x (1 / 3)) (FracPowE x (2 / 3)) :: Exp Double)
            `shouldNotBe` x
        it "Does not divide rational powers into an integral power" $
          simplify (FracBinopE FDiv (FracPowE x (4 / 3)) (FracPowE x (1 / 3)) :: Exp Double)
            `shouldNotBe` x
        it "Combines identical rational powers as a square of the original expression" $
          simplify (NumBinopE Mul (FracPowE x (1 / 2)) (FracPowE x (1 / 2)) :: Exp Double) @?=
            NatPowE (FracPowE x (1 / 2)) 2
        it "Combines powers when their sum remains nonintegral" $
          simplify (NumBinopE Mul x (FracPowE x (1 / 2)) :: Exp Double) @?= FracPowE x (3 / 2)
        it "Terminates when ordering rational powers with constant bases" $
          property $ within 1000000 $
            eval (simplify (NumBinopE Mul (FracPowE 0 (1/2)) (FloatUnopE Sqrt 1)) :: Exp Double) === 0
        it "log x + log y = log (x*y)" $
          simplify (log x + log y :: Exp Double) @?= log (x*y)
        it "log x - log y = log (x/y)" $
          simplify (log x - log y :: Exp Double) @?= log (x/y)
        it "(sin x) ** 2 + (cos x) ** 2 = 1" $
          simplify (sin x ** 2 + cos x ** 2 :: Exp Double) @?= 1
  where
    e, x, y, z :: Floating a => Exp a
    e = ConstE E
    x = VarE "x"
    y = VarE "y"
    z = VarE "z"

popEvalSimplifyEquiv :: Double -> Int -> DExp -> Property
popEvalSimplifyEquiv eps ms (DExp e) =
    counterexample (prettyCompact $ text "Expression:" <+> ppr e) $
    counterexample ("Expression: " ++ show e) $
    within ms $
    counterexample (prettyCompact $ text "Simplified:" <+> ppr e') $
    counterexample (prettyCompact $ text "Simplified and evaluated:" <+> ppr e1) $
    counterexample (prettyCompact $ text "Evaluated:" <+> ppr e2) $
    property (isExactE e') .&&. equiv eps e1 e2
  where
     e' = simplify e
     e1 = eval e'
     e2 = eval e

equiv :: Double -> Exp Double -> Exp Double -> Property
equiv eps (ConstE x) (ConstE y)
  | any nonfinite [eps, x', y'] || eps <= 0 = property False
  | d == 0                                  = property True
  | otherwise                               = property $ n / d < eps
  where
    x' = fromConst x
    y' = fromConst y
    n = abs (x' - y')
    d = max (abs x') (abs y')

    nonfinite a = isNaN a || isInfinite a

equiv _   e1         e2         = counterexample ("Expected finite constants: " ++ show (e1, e2)) False
