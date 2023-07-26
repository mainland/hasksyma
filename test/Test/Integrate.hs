{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  Test.Integrate
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Integrate where

import Control.Applicative ( (<|>), empty )
import Test.HUnit ( (@?=) )
import Test.Hspec ( describe, it, Spec )

import Hasksyma.Const
import Hasksyma.Diff ( diff )
import Hasksyma.Exp ( Exp(..) )
import Hasksyma.Integrate
import Hasksyma.Simplify

integral :: (Show a, Floating a, Floating (Const a)) => Exp a -> Exp a -> Exp a
integral e (VarE x) = IntE Nothing e x
integral _ x        = error $ show x ++ " is not a variable"

integrate :: (Ord a, Floating a, Floating (Const a), IsConst a)
          => Exp a
          -> Exp a
integrate e | e' == e   = e
            | otherwise = integrate e'
  where
    e' = mapExp int1 e

    int1 (IntE Nothing e x) = case heuristicIntegrate e x of
                                [] -> IntE Nothing e x
                                e':_ -> e'

    int1 e = simp e

integrateTests :: Spec
integrateTests = describe "Integration" $ do
    it "int x^2 dx = x^3/3" $
        integrate (integral (x^2) x :: Exp Double) @?= x^3/3
    it "int x * sin(x^2) dx = -1/2*cos (x^2)" $
        integrate (integral (x * sin(x^2)) x :: Exp Double) @?= -1/2*cos (x^2)
  where
    a,b,c, x, y, z :: Exp a
    a = VarE "a"
    b = VarE "b"
    c = VarE "c"
    x = VarE "x"
    y = VarE "y"
    z = VarE "z"
