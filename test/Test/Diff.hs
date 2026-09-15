{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  Test.Simplify
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Diff where

import           Control.Monad     (forM_)
import           Data.Complex      (Complex (..))
import           Test.Hspec        (Spec, describe, it)
import           Test.HUnit        ((@?=))

import           Hasksyma.Const    (Const (..), IsConst (fromConst))
import           Hasksyma.Diff     (diff)
import           Hasksyma.Eval     (eval)
import           Hasksyma.Exp      (Exp (ConstE, DiffE, FloatBinopE, FracBinopE, FracPowE, IntPowE, NatPowE, NumBinopE, VarE),
                                    FloatBinop (Pow), FracBinop (FDiv), NumBinop (Mul), sameExp)
import           Hasksyma.Simplify (mapExp, simp, simplify, simplify')

diffTests :: Spec
diffTests = describe "Differentiation" $ do
    describe "Zero derivative terms" $ do
      forM_ [("natural", (`NatPowE` 0)), ("integer", (`IntPowE` 0)),
             ("rational", (`FracPowE` 0)),
             ("general integer", \u -> FloatBinopE Pow u (ConstE (IntegerC 0))),
             ("general rational", \u -> FloatBinopE Pow u (ConstE (RationalC 0)))] $ \(name, power) ->
        it ("differentiates " ++ name ++ " zero powers without introducing a reciprocal") $
          simp (diff (power x) x :: Exp Double) @?= 0
      it "omits the constant exponent's logarithmic term at a negative real base" $
        valueAt (-2) (simplify (diff (FloatBinopE Pow x y) x)) @?= 12
      it "omits a zero inner derivative in the chain rule" $
        simplify (diff (sin y) x :: Exp Double) @?= 0
      it "removes zero derivative summands before a surrounding product distributes" $
        forM_ [(2*y, 2*x), (2+y, x), (y-2, x)] $ \(u, expected) ->
          simplify (x * diff u y :: Exp Double) @?= expected
      it "allows domain extension when simplifying a zero product's derivative" $
        let derivative = simplify (diff (NumBinopE Mul 0 (IntPowE x (-1))) x)
        in sameExp derivative (0 :: Exp Double) @?= True
      it "retains the reciprocal derivative with a constant numerator" $
        valueAt 2 (simplify (diff (FracBinopE FDiv 1 x) x)) @?= -1/4
    describe "Logarithmic absolute values" $ do
      forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) ->
        it (name ++ " retains the unresolved complex absolute-value derivative") $
          let z = VarE "z" :: Exp (Complex Double)
          in sameExp (transform (diff (log (abs z)) z))
               (FracBinopE FDiv (DiffE (abs z) "z") (abs z)) @?= True
      it "also leaves the real absolute-value derivative unresolved without domain evidence" $
        sameExp (simplify (diff (log (abs x)) x :: Exp Double))
          (FracBinopE FDiv (DiffE (abs x) "x") (abs x)) @?= True
    it "diff (x ^ 0) x = 0" $
        simp (diff (NatPowE x 0) x :: Exp Double) @?= 0
    it "diff (x ^ 1) x = 1" $
        simplify (diff (NatPowE x 1) x :: Exp Double) @?= 1
    it "diff (x ^ 3) x = 3*x^2" $
        simplify (diff (NatPowE x 3) x :: Exp Double) @?= NumBinopE Mul 3 (NatPowE x 2)
    it "diff (x ^^ (-2)) x = -2*x^^(-3)" $
        simplify (diff (IntPowE x (-2)) x :: Exp Double) @?=
          simplify (NumBinopE Mul (-2) (IntPowE x (-3)))
    it "diff (x ** (1/2)) x = (1/2)*x**(-1/2)" $
        simplify (diff (FracPowE x (1 / 2)) x :: Exp Double) @?=
          simplify (NumBinopE Mul (ConstE (RationalC (1 / 2))) (FracPowE x (-1 / 2)))
    it "diff (x + x) x = 2" $
        simplify (diff (x + x) x :: Exp Double) @?= 2
    it "diff (a * x ^ 2 + b * x + c) x = 2*a*x + b" $
        simplify (diff (a * x ^ (2 :: Integer) + b * x + c) x :: Exp Double) @?= 2*a*x + b
    it "log (diff (x + x) x / 2) = 0" $
        simplify (log (diff (x + x) x / 2) :: Exp Double) @?= 0
    it "simplifies logarithm arguments without combining the logarithms" $
        simplify ((log (x + x) - log x) :: Exp Double) @?= log (2*x) - log x
    it "x ** cos pi = 1 / x" $
        simplify (x ** cos pi :: Exp Double) @?= IntPowE x (-1)
    it "diff (3*x^2 + 2*x + 1) x = 6*x + 2" $
        simplify (diff (3*x^(2 :: Integer) + 2*x + 1) x :: Exp Double) @?= 6*x + 2
    it "differentiates 3*x + cos x/x without cancelling the denominator" $
        simplify (diff (3*x + cos x/x) x :: Exp Double) @?=
          simplify (-x*sin x/NatPowE x 2 - cos x/NatPowE x 2 + 3)
    it "differentiates cos x/x without cancelling the denominator" $
        simplify (diff (cos x / x) x :: Exp Double) @?=
          simplify (-x*sin x/NatPowE x 2 - cos x/NatPowE x 2)
    it "sin (x + x)^2 + cos (diff (x^2) x)^2 = 1" $
        simplify (sin (x + x)^(2 :: Integer) + cos (diff (x^(2 :: Integer)) x)^(2 :: Integer) :: Exp Double) @?= 1
    it "sin (x + x) * sin (diff (x^2) x) + cos(2*x) * cos(x * diff (2*y) y) = 1" $
        simplify (sin (x + x) * sin (diff (x^(2 :: Integer)) x) + cos(2*x) * cos(x * diff (2*y) y) :: Exp Double) @?= 1
  where
    valueAt :: Double -> Exp Double -> Double
    valueAt point e = case eval (mapExp replace e) of
                       ConstE constant -> fromConst constant
                       result          -> error (show result)
      where
        replace (VarE "x") = ConstE (Const point)
        replace (VarE "y") = 3
        replace other      = other

    a,b,c, x, y :: Exp a
    a = VarE "a"
    b = VarE "b"
    c = VarE "c"
    x = VarE "x"
    y = VarE "y"
