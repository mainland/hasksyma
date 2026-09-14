-- SPDX-License-Identifier: BSD-3-Clause

{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- |
-- Module      : Test.Arbitrary
-- Copyright   : (c) 2023 Drexel University
-- License     : BSD-3-Clause
-- Maintainer  : mainland@drexel.edu
module Test.Arbitrary () where

import           Data.Complex    (Complex)
import           Hasksyma.Const  (Const (..))
import           Test.QuickCheck (Arbitrary (arbitrary), frequency, oneof)

instance Arbitrary (Const Integer) where
  arbitrary = oneof [Const <$> arbitrary, IntegerC <$> arbitrary]

instance Arbitrary (Const Rational) where
  arbitrary = oneof [Const <$> arbitrary, IntegerC <$> arbitrary, RationalC <$> arbitrary]

instance Arbitrary (Const Float) where
  arbitrary =
    frequency
      [ (10, Const <$> arbitrary),
        (1, pure E),
        (1, Pi <$> arbitrary),
        (10, IntegerC <$> arbitrary),
        (10, RationalC <$> arbitrary)
      ]

instance Arbitrary (Const Double) where
  arbitrary =
    frequency
      [ (10, Const <$> arbitrary),
        (1, pure E),
        (1, Pi <$> arbitrary),
        (10, IntegerC <$> arbitrary),
        (10, RationalC <$> arbitrary)
      ]

instance Arbitrary (Const (Complex Float)) where
  arbitrary =
    frequency
      [ (10, Const <$> arbitrary),
        (1, pure E),
        (1, Pi <$> arbitrary),
        (10, IntegerC <$> arbitrary),
        (10, RationalC <$> arbitrary)
      ]

instance Arbitrary (Const (Complex Double)) where
  arbitrary =
    frequency
      [ (10, Const <$> arbitrary),
        (1, pure E),
        (1, Pi <$> arbitrary),
        (10, IntegerC <$> arbitrary),
        (10, RationalC <$> arbitrary)
      ]
