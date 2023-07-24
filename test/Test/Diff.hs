{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  Test.Simplify
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Diff where

import Control.Applicative ( (<|>), empty )
import Test.HUnit ( (@?=) )
import Test.Hspec ( describe, it, Spec )

import Hasksyma.Diff ( diff )
import Hasksyma.Exp ( Exp(VarE) )
import Hasksyma.Simplify ( simplify )

diffTests :: Spec
diffTests = describe "Differentiation" $ do
    it "diff (x + x) x = 2" $
        simplify (diff (x + x) x :: Exp Double) @?= 2
    it "diff (a * x ^ 2 + b * x + c) x = 2*a*x + b" $
        simplify (diff (a * x ^ 2 + b * x + c) x :: Exp Double) @?= 2*a*x + b
    it "log ((diff (x + x) x) / 2) = 0" $
        simplify (log ((diff (x + x) x) / 2) :: Exp Double) @?= 0
    it "log (x + x) - log x = log 2" $
        simplify ((log (x + x) - log x) :: Exp Double) @?= log 2
    it "x ** cos pi = 1 / x" $
        simplify (x ** cos pi :: Exp Double) @?= x ^^ (-1)
    it "diff (3*x^2 + 2*x + 1) x = 6*x + 2" $
        simplify (diff (3*x^2 + 2*x + 1) x :: Exp Double) @?= 6*x + 2
    it "diff (3*x + cos x/x) x = -sin x/x - cos x /x^2 + 3" $
        simplify (diff (3*x + cos x/x) x :: Exp Double) @?= -sin x/x - cos x/x^2 + 3
    it "diff (cos x / x) x = -sin x/x - cos x /x^2" $
        simplify (diff (cos x / x) x :: Exp Double) @?= -sin x/x - cos x /x^2
    it "sin (x + x)^2 + cos (diff (x^2) x)^2 = 1" $
        simplify (sin (x + x)^2 + cos (diff (x^2) x)^2 :: Exp Double) @?= 1
    it "sin (x + x) * sin (diff (x^2) x) + cos(2*x) * cos(x * diff (2*y) y) = 1" $
        simplify (sin (x + x) * sin (diff (x^2) x) + cos(2*x) * cos(x * diff (2*y) y) :: Exp Double) @?= 1
  where
    a,b,c, x, y, z :: Exp a
    a = VarE "a"
    b = VarE "b"
    c = VarE "c"
    x = VarE "x"
    y = VarE "y"
    z = VarE "z"
