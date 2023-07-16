{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      :  Test.Simplify
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Exact where

import Test.Hspec ( describe, it, Spec )
import Test.QuickCheck
    ( Arbitrary(arbitrary), oneof, Testable(property) )

import Hasksyma.Const

-- | An exact value of type @'Const' a@
newtype Exact a = Exact { unExact :: Const a }
  deriving (Eq, Ord, Show, Num, Integral, Enum, Real, Fractional)

instance Arbitrary (Exact Integer) where
    arbitrary = Exact . IntegerC <$> arbitrary

instance Arbitrary (Exact Rational) where
    arbitrary = Exact <$> oneof [ IntegerC <$> arbitrary
                                , RationalC <$> arbitrary
                                ]

instance Arbitrary (Exact Float) where
    arbitrary = Exact <$> oneof [ IntegerC <$> arbitrary
                                , RationalC <$> arbitrary
                                ]

instance Arbitrary (Exact Double) where
    arbitrary = Exact <$> oneof [ IntegerC <$> arbitrary
                                , RationalC <$> arbitrary
                                ]

prop_num_exact :: (IsConst a, Num a)
               => (forall b . Num b => b -> b -> b)
               -> Exact a -> Exact a -> Bool
prop_num_exact f (Exact x) (Exact y) = isExact (f x y)

prop_pi_num_exact :: (forall b . Num b => b -> b -> b)
                  -> Rational -> Rational -> Bool
prop_pi_num_exact f k1 k2 = isExact (f (fromRational k1 * pi :: Const Double) (pi * fromRational k2))

exactConstTests :: Spec
exactConstTests = describe "Computation with exact constants" $ do
    it "Addition of exact constants produces exact constant" $
        property (prop_num_exact (+) :: Exact Double -> Exact Double -> Bool)
    it "Subtraction of exact constants produces exact constant" $
        property (prop_num_exact (-) :: Exact Double -> Exact Double -> Bool)
    it "Multiplication of exact constants produces exact constant" $
        property (prop_num_exact (*) :: Exact Double -> Exact Double -> Bool)
    it "Addition of multiples of pi produces exact constant" $
        property (prop_pi_num_exact (+))
    it "Subtraction of multiples of pi produces exact constant" $
        property (prop_pi_num_exact (-))
