{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  Test.Integrate
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Integrate where

import           Test.Hspec         (Spec, describe, it)
import           Test.HUnit         ((@?=))

import           Hasksyma.Const
import           Hasksyma.Exp       (Exp (..))
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
integrateTests = describe "Integration" $ do
    it "int x^2 dx = x^3/3" $
        integrate (integral (x^(2 :: Integer)) x :: Exp Double) @?= IntPowE x 3/3
    it "int x * sin(x^2) dx = -1/2*cos (x^2)" $
        integrate (integral (x * sin(x^(2 :: Integer))) x :: Exp Double) @?=
          -(ConstE (RationalC (1/2)) * cos (IntPowE x 2))
  where
    x :: Exp a
    x = VarE "x"
