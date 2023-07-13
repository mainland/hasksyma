{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      :  Hasksyma.Const
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Hasksyma.Const (
  Const(..),
  IsConst(..),
  isExact
) where

import Data.Complex ( Complex(..) )
import IHaskell.Display ( IHaskellDisplay(..) )
import Test.QuickCheck ( Arbitrary(arbitrary), oneof )
import Text.PrettyPrint.Mainland ( (<+>), parensIf, text )
import Text.PrettyPrint.Mainland.Class ( Pretty(pprPrec) )

import Hasksyma.LaTeX ( displayMath, PrettyTeX(tppr) )
import Hasksyma.Pretty ( appPrec, appPrec1 )

data Const a where
    Const     :: a -> Const a
    IntegerC  :: Num a => Integer -> Const a
    RationalC :: Fractional a => Rational -> Const a

-- | Convert between @a@ and @'Const' a@
class IsConst a where
    -- | Project a value of type @a@ from a @'Const' a@
    fromConst :: Const a -> a
    fromConst (Const x) = x
    fromConst _         = error "can't happen"

    -- | Construct a value of type @'Const' a@ from a value of type @a@
    toConst :: a -> Const a
    toConst x = Const x

-- | Return 'True' if constant is exact
isExact :: Const a -> Bool
isExact IntegerC{}  = True
isExact RationalC{} = True
isExact _           = False

-- | Convert constants to a "canonical" form suitable for comparison.
joinWith :: IsConst a
         => (Const a -> Const a -> b)
         -> Const a
         -> Const a
         -> b
joinWith f x@Const{}     y@Const{}     = f x y
joinWith f x@IntegerC{}  y@IntegerC{}  = f x y
joinWith f x@RationalC{} y@RationalC{} = f x y
joinWith f (IntegerC x)  y@RationalC{} = f (RationalC (fromInteger x)) y
joinWith f x@RationalC{} (IntegerC y)  = f x (RationalC (fromInteger y))
joinWith f x             y             = f (Const (fromConst x)) (Const (fromConst y))

deriving instance Show a => Show (Const a)

instance (Eq a, IsConst a) => Eq (Const a) where
    Const x     == Const y     = x == y
    IntegerC x  == IntegerC y  = x == y
    RationalC x == RationalC y = x == y
    x           == y           = joinWith (==) x y

instance (Ord a, IsConst a) => Ord (Const a) where
    compare (Const x)     (Const y)     = compare x y
    compare (IntegerC x)  (IntegerC y)  = compare x y
    compare (RationalC x) (RationalC y) = compare x y
    compare x             y             = joinWith compare x y

instance IsConst Int where
    fromConst (Const x)    = x
    fromConst (IntegerC x) = fromInteger x
    fromConst _            = error "can't happen"

    toConst = IntegerC . fromIntegral

instance IsConst Integer where
    fromConst (Const x)    = x
    fromConst (IntegerC x) = fromInteger x
    fromConst _            = error "can't happen"

    toConst = IntegerC

instance IsConst Float where
    fromConst (Const x)     = x
    fromConst (IntegerC x)  = fromInteger x
    fromConst (RationalC x) = fromRational x

instance IsConst Double where
    fromConst (Const x)     = x
    fromConst (IntegerC x)  = fromInteger x
    fromConst (RationalC x) = fromRational x

instance IsConst Rational where
    fromConst (Const x)     = x
    fromConst (IntegerC x)  = fromInteger x
    fromConst (RationalC x) = x

    toConst = RationalC

instance RealFloat a => IsConst (Complex a) where
    fromConst (Const x)     = x
    fromConst (IntegerC x)  = fromInteger x
    fromConst (RationalC x) = fromRational x

-- | Lift a unary operation on @'Num'@ type class to the type @'Const' a@
liftNum :: (IsConst b, Num b)
        => (forall a . Num a => a -> a)
        -> Const b
        -> Const b
liftNum f (Const x)     = Const (f x)
liftNum f (IntegerC x)  = IntegerC (f x)
liftNum f (RationalC x) = RationalC (f x)

-- | Lift a binary operation on @'Num'@ type class to the type @'Const' a@
liftNum2 :: (IsConst b, Num b)
         => (forall a . Num a => a -> a -> a)
         -> Const b
         -> Const b
         -> Const b
liftNum2 f (Const x)     (Const y)     = Const (f x y)
liftNum2 f (IntegerC x)  (IntegerC y)  = IntegerC (f x y)
liftNum2 f (RationalC x) (RationalC y) = RationalC (f x y)
liftNum2 f x             y             = joinWith (liftNum2 f) x y

liftIntegral2 :: (IsConst b, Integral b)
              => (forall a . Integral a => a -> a -> a)
              -> Const b
              -> Const b
              -> Const b
-- | Lift a binary operation on 'Integral' to the type 'b
liftIntegral2 f (Const x) (Const y) = Const (f x y)
liftIntegral2 f x          y        = joinWith (liftIntegral2 f) x y

instance (IsConst a, Num a) => Num (Const a) where
    x + y = liftNum2 (+) x y

    x - y = liftNum2 (-) x y

    x * y = liftNum2 (*) x y

    negate x = liftNum negate x

    abs x = liftNum abs x

    signum = liftNum signum

    fromInteger x = IntegerC x

instance (IsConst a, Real a) => Real (Const a) where
    toRational (Const x)     = toRational x
    toRational (IntegerC x)  = fromInteger x
    toRational (RationalC x) = x

instance Enum a => Enum (Const a) where
    toEnum x = Const (toEnum x)

    fromEnum (Const x)     = fromEnum x
    fromEnum (IntegerC x)  = fromEnum x
    fromEnum (RationalC x) = fromEnum x

instance (IsConst a, Integral a) => Integral (Const a) where
    quot = liftIntegral2 quot
    rem  = liftIntegral2 rem
    div  = liftIntegral2 div
    mod  = liftIntegral2 mod

    x `quotRem` y = (x `quot` y, x `rem` y)

    x `divMod` y = (x `div` y, x `mod` y)

    toInteger (Const x)    = toInteger x
    toInteger (IntegerC x) = x
    toInteger RationalC{}  = error "can't happen"

-- | Lift a unary operation on 'Num' to the type 'Const a'
liftFractional :: (IsConst b, Fractional b)
               => (forall a . Fractional a => a -> a)
               -> Const b
               -> Const b
liftFractional f (Const x)     = Const (f x)
liftFractional f (IntegerC x)  = RationalC (f (fromInteger x))
liftFractional f (RationalC x) = RationalC (f x)

-- | Lift a binary operation on 'Num' to the type 'Const a'
liftFractional2 :: (IsConst b, Fractional b)
                => (forall a . Fractional a => a -> a -> a)
                -> Const b
                -> Const b
                -> Const b
liftFractional2 f (Const x)     (Const y)     = Const (f x y)
liftFractional2 f (IntegerC x)  (IntegerC y)  = RationalC (f (fromInteger x) (fromInteger y))
liftFractional2 f (RationalC x) (RationalC y) = RationalC (f x y)
liftFractional2 f x             y             = joinWith (liftFractional2 f) x y

instance (IsConst a, Fractional a) => Fractional (Const a) where
    x / y = liftFractional2 (/) x y

    recip  = liftFractional recip

    fromRational x = RationalC x

liftFloating :: (IsConst b, Floating b)
             => (forall a . Floating a => a -> a)
             -> Const b
             -> Const b
liftFloating f (Const x) = Const (f x)
liftFloating f x         = toConst (f (fromConst x))

liftFloating2 :: (IsConst b, Floating b)
              => (forall a . Floating a => a -> a -> a)
              -> Const b
              -> Const b
              -> Const b
liftFloating2 f (Const x) (Const y) = Const (f x y)
liftFloating2 f x         y         = toConst (f (fromConst x) (fromConst y))

instance Floating (Const Float) where
    pi = pi

    exp  = liftFloating exp
    log  = liftFloating log

    sqrt = liftFloating sqrt

    (**) = liftFloating2 (**)

    sin = liftFloating sin
    cos = liftFloating cos

    tan = liftFloating tan

    asin = liftFloating asin
    acos = liftFloating acos
    atan = liftFloating atan

    sinh = liftFloating sinh
    cosh = liftFloating cosh
    tanh = liftFloating tanh

    asinh = liftFloating asinh
    acosh = liftFloating acosh
    atanh = liftFloating atanh

instance Floating (Const Double) where
    pi = pi

    exp  = liftFloating exp
    log  = liftFloating log

    sqrt = liftFloating sqrt

    (**) = liftFloating2 (**)

    sin = liftFloating sin
    cos = liftFloating cos

    tan = liftFloating tan

    asin = liftFloating asin
    acos = liftFloating acos
    atan = liftFloating atan

    sinh = liftFloating sinh
    cosh = liftFloating cosh
    tanh = liftFloating tanh

    asinh = liftFloating asinh
    acosh = liftFloating acosh
    atanh = liftFloating atanh

instance RealFloat a => Floating (Const (Complex a)) where
    pi = pi

    exp  = liftFloating exp
    log  = liftFloating log

    sqrt = liftFloating sqrt

    (**) = liftFloating2 (**)

    sin = liftFloating sin
    cos = liftFloating cos

    tan = liftFloating tan

    asin = liftFloating asin
    acos = liftFloating acos
    atan = liftFloating atan

    sinh = liftFloating sinh
    cosh = liftFloating cosh
    tanh = liftFloating tanh

    asinh = liftFloating asinh
    acosh = liftFloating acosh
    atanh = liftFloating atanh

instance Arbitrary (Const Integer) where
    arbitrary = oneof [Const <$> arbitrary, IntegerC <$> arbitrary]

instance Arbitrary (Const Rational) where
    arbitrary = oneof [Const <$> arbitrary, IntegerC <$> arbitrary, RationalC <$> arbitrary]

instance Arbitrary (Const Float) where
    arbitrary = oneof [Const <$> arbitrary, IntegerC <$> arbitrary, RationalC <$> arbitrary]

instance Arbitrary (Const Double) where
    arbitrary = oneof [Const <$> arbitrary, IntegerC <$> arbitrary, RationalC <$> arbitrary]

instance Arbitrary (Const (Complex Float)) where
    arbitrary = oneof [Const <$> arbitrary, IntegerC <$> arbitrary, RationalC <$> arbitrary]

instance Arbitrary (Const (Complex Double)) where
    arbitrary = oneof [Const <$> arbitrary, IntegerC <$> arbitrary, RationalC <$> arbitrary]

instance Pretty a => Pretty (Const a) where
    pprPrec p (Const x)     = pprPrec p x
    pprPrec p (IntegerC x)  = pprPrec p x
    pprPrec p (RationalC x) = parensIf (p > appPrec) $
                              text "fromRational" <+> pprPrec appPrec1 x

instance PrettyTeX a => PrettyTeX (Const a) where
    tppr (Const x)     = tppr x
    tppr (IntegerC x)  = tppr x
    tppr (RationalC x) = tppr x

instance PrettyTeX a => IHaskellDisplay (Const a) where
    display = displayMath
