{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  Test.PEval
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.PEval where

import Control.Applicative ( (<|>), empty )
import Data.Proxy ( Proxy(Proxy) )
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

prop_nonnegative_pow :: (Num a, IsConst a, Eq a, Show a)
                     => proxy a
                     -> Exp a -> NonNegative Integer -> Property
prop_nonnegative_pow _ e (NonNegative 0) = e^0 === 1
prop_nonnegative_pow _ e (NonNegative 1) = e^1 === e
prop_nonnegative_pow _ e (NonNegative n) = e^n === IntPowE e n

prop_integral_pow :: (Fractional a, IsConst a, Eq a, Show a)
                  => proxy a
                  -> Exp a -> Integer -> Property
prop_integral_pow _ e (-1) = e^^(-1) === recip e
prop_integral_pow _ e 0    = e^^0 === 1
prop_integral_pow _ e 1    = e^^1 === e
prop_integral_pow _ e n | n > 0     = e^^n === IntPowE e n
                        | otherwise = e^^n === FracPowE e n

powPevalTests :: SpecWith ()
powPevalTests =
    describe "^/^^ partial evaluation" $ do
      describe "Integer" $ do
        it "non-negative integral powers" $
          property $ prop_nonnegative_pow (Proxy :: Proxy Integer) (x-1)

      describe "Rational" $ do
        it "non-negative integral powers" $
          property $ prop_nonnegative_pow (Proxy :: Proxy Rational) (x-1)
        it "integral powers" $
          property $ prop_integral_pow (Proxy :: Proxy Rational) (x-1)

      describe "Double" $ do
        it "non-negative integral powers" $
          property $ prop_nonnegative_pow (Proxy :: Proxy Double) (x-1)
        it "integral powers" $
          property $ prop_integral_pow (Proxy :: Proxy Double) (x-1)
  where
    x, y, z :: Exp a
    x = VarE "x"
    y = VarE "y"
    z = VarE "z"
