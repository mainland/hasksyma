{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  Test.Simplify
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Simplify where

import Control.Applicative ( (<|>), empty )
import Test.HUnit
import Test.Hspec
import Test.QuickCheck
import Text.PrettyPrint.Mainland ( (<+>), prettyCompact, text )
import Text.PrettyPrint.Mainland.Class ( ppr )

import Hasksyma.Const
import Hasksyma.Exp
import Hasksyma.Eval
import Hasksyma.Simplify

import Test.Eval

simplifyTests :: Spec
simplifyTests = describe "Simplification" $ do
    norvigTests
    it "Simplification evaluates all constants" $
        property $ forAllShrinkBlind arbitrary shrink $ pop_eval_simplify_equiv eps tensec
  where
    eps :: Double
    eps = 1e-12

    tensec :: Int
    tensec = 10 * 1000000

norvigTests = describe "Simplification tests from PAIP 8.2" $ do
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
  where
    x, y, z :: Exp a
    x = VarE "x"
    y = VarE "y"
    z = VarE "z"

pop_eval_simplify_equiv :: Double -> Int -> DExp -> Property
pop_eval_simplify_equiv eps ms (DExp e) =
    counterexample (prettyCompact $ text "Expression:" <+> ppr e) $
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
  | d > 0     = property $ n / d < eps
  | otherwise = property True
  where
    x' = fromConst x
    y' = fromConst y
    n = abs (x' - y')
    d = max (abs x') (abs y')

equiv _ e1 e2 = e1 === e2
