{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  Test.Simplify
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Diff where

import           Test.Hspec        (Spec, describe, it)
import           Test.HUnit        ((@?=))

import           Hasksyma.Const    (Const (RationalC))
import           Hasksyma.Diff     (diff)
import           Hasksyma.Exp      (Exp (ConstE, FracPowE, IntPowE, NatPowE, NumBinopE, VarE),
                                    NumBinop (Mul))
import           Hasksyma.Simplify (simp, simplify)

diffTests :: Spec
diffTests = describe "Differentiation" $ do
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
    it "log (x + x) - log x = log 2" $
        simplify ((log (x + x) - log x) :: Exp Double) @?= log 2
    it "x ** cos pi = 1 / x" $
        simplify (x ** cos pi :: Exp Double) @?= IntPowE x (-1)
    it "diff (3*x^2 + 2*x + 1) x = 6*x + 2" $
        simplify (diff (3*x^(2 :: Integer) + 2*x + 1) x :: Exp Double) @?= 6*x + 2
    it "diff (3*x + cos x/x) x = -sin x/x - cos x /x^2 + 3" $
        simplify (diff (3*x + cos x/x) x :: Exp Double) @?= -sin x/x - cos x/NatPowE x 2 + 3
    it "diff (cos x / x) x = -sin x/x - cos x /x^2" $
        simplify (diff (cos x / x) x :: Exp Double) @?= -sin x/x - cos x/NatPowE x 2
    it "sin (x + x)^2 + cos (diff (x^2) x)^2 = 1" $
        simplify (sin (x + x)^(2 :: Integer) + cos (diff (x^(2 :: Integer)) x)^(2 :: Integer) :: Exp Double) @?= 1
    it "sin (x + x) * sin (diff (x^2) x) + cos(2*x) * cos(x * diff (2*y) y) = 1" $
        simplify (sin (x + x) * sin (diff (x^(2 :: Integer)) x) + cos(2*x) * cos(x * diff (2*y) y) :: Exp Double) @?= 1
  where
    a,b,c, x, y :: Exp a
    a = VarE "a"
    b = VarE "b"
    c = VarE "c"
    x = VarE "x"
    y = VarE "y"
