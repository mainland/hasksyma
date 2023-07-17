{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

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
#if defined(CYCLOTOMIC)
import Data.Complex.Cyclotomic ( Cyclotomic(..) )
import qualified Data.Complex.Cyclotomic as Cyc
import qualified Data.Map as Map
import Data.Maybe ( fromJust )
import Data.Number.RealCyclotomic ( RealCyclotomic(..) )
import qualified Data.Number.RealCyclotomic as RealCyc
#endif /* defined(CYCLOTOMIC) */
import Text.LaTeX.Base.Class ( comm1, commS )
import Text.PrettyPrint.Mainland ( (<+>), char, parensIf, text )
#if defined(CYCLOTOMIC)
import Text.PrettyPrint.Mainland ( Doc )
#endif /* defined(CYCLOTOMIC) */
import Text.PrettyPrint.Mainland.Class ( Pretty(pprPrec) )
#if defined(CYCLOTOMIC)
import Text.PrettyPrint.Mainland.Class ( Pretty(ppr) )
#endif /* defined(CYCLOTOMIC) */
import Test.QuickCheck ( Arbitrary(arbitrary), frequency, oneof )

import Hasksyma.LaTeX ( displayMath, PrettyTeX(tppr) )
import Hasksyma.Pretty ( appPrec, appPrec1, mulPrec, mulPrec1 )
#if defined(CYCLOTOMIC)
import Hasksyma.Pretty ( addPrec )
#endif /* defined(CYCLOTOMIC) */

data Const a where
    Const     :: a -> Const a
    Pi        :: Floating a => Rational -> Const a
    E         :: Floating a => Const a
    IntegerC  :: Num a => Integer -> Const a
    RationalC :: Fractional a => Rational -> Const a
#if defined(CYCLOTOMIC)
    RealCycC  :: RealFloat a => RealCyclotomic -> Const a
    CycC      :: RealFloat a => Cyclotomic -> Const (Complex a)
#endif /* defined(CYCLOTOMIC) */

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
isExact Pi{}        = True
isExact E{}         = True
isExact IntegerC{}  = True
isExact RationalC{} = True
#if defined(CYCLOTOMIC)
isExact RealCycC{}  = True
isExact CycC{}      = True
#endif /* defined(CYCLOTOMIC) */
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
#if defined(CYCLOTOMIC)
joinWith f x@RealCycC{}  y@RealCycC{}  = f x y
joinWith f x@CycC{}      y@CycC{}      = f x y
#endif /* defined(CYCLOTOMIC) */

joinWith f (IntegerC x)  y@RationalC{} = f (RationalC (fromInteger x)) y
joinWith f x@RationalC{} (IntegerC y)  = f x (RationalC (fromInteger y))

#if defined(CYCLOTOMIC)
joinWith f x@RealCycC{}  (IntegerC y)  = f x (RealCycC (fromInteger y))
joinWith f (IntegerC x)  y@RealCycC{}  = f (RealCycC (fromInteger x)) y
joinWith f x@RealCycC{}  (RationalC y) = f x (RealCycC (fromRational y))
joinWith f (RationalC x) y@RealCycC{}  = f (RealCycC (fromRational x)) y

joinWith f x@CycC{}      (IntegerC y)  = f x (CycC (fromInteger y))
joinWith f (IntegerC x)  y@CycC{}      = f (CycC (fromInteger x)) y
joinWith f x@CycC{}      (RationalC y) = f x (CycC (fromRational y))
joinWith f (RationalC x) y@CycC{}      = f (CycC (fromRational x)) y
#endif /* defined(CYCLOTOMIC) */

joinWith f x             y             = f (Const (fromConst x)) (Const (fromConst y))

deriving instance Show a => Show (Const a)

instance (Eq a, IsConst a) => Eq (Const a) where
    Const x     == Const y     = x == y
    IntegerC x  == IntegerC y  = x == y
    RationalC x == RationalC y = x == y
#if defined(CYCLOTOMIC)
    CycC x      == CycC y      = x == y
    RealCycC x  == RealCycC y  = x == y
#endif /* defined(CYCLOTOMIC) */
    x           == y           = joinWith (==) x y

instance (Ord a, IsConst a) => Ord (Const a) where
    compare (Const x)     (Const y)     = compare x y
    compare (IntegerC x)  (IntegerC y)  = compare x y
    compare (RationalC x) (RationalC y) = compare x y
#if defined(CYCLOTOMIC)
    compare (RealCycC x)  (RealCycC y)  = compare (RealCyc.toReal x :: Double) (RealCyc.toReal y :: Double)
    compare CycC{}        CycC{}        = error "incomparable"
#endif /* defined(CYCLOTOMIC) */
    compare x             y             = joinWith compare x y

#if defined(CYCLOTOMIC)
-- | Export a 'Cyclotomic' as an inexact complex number. This function avoids
-- some error that `Data.Complex.Cyclotomic.toComplex` introduces.
fromCyclotomic :: RealFloat a => Cyclotomic -> Complex a
fromCyclotomic x = re :+ im
  where
    re = fromRealCyclotomic (Cyc.real x)
    im = fromRealCyclotomic (Cyc.imag x)

fromRealCyclotomic :: forall a . RealFloat a => Cyclotomic -> a
fromRealCyclotomic x = fromJust (Cyc.toReal x :: Maybe a)
#endif /* defined(CYCLOTOMIC) */

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
    fromConst (Pi k)        = fromRational k * pi
    fromConst E             = exp 1
    fromConst (IntegerC x)  = fromInteger x
    fromConst (RationalC x) = fromRational x
#if defined(CYCLOTOMIC)
    fromConst (RealCycC x)  = RealCyc.toReal x
#endif /* defined(CYCLOTOMIC) */

instance IsConst Double where
    fromConst (Const x)     = x
    fromConst (Pi k)        = fromRational k * pi
    fromConst E             = exp 1
    fromConst (IntegerC x)  = fromInteger x
    fromConst (RationalC x) = fromRational x
#if defined(CYCLOTOMIC)
    fromConst (RealCycC x)   = RealCyc.toReal x
#endif /* defined(CYCLOTOMIC) */

instance IsConst Rational where
    fromConst (Const x)     = x
    fromConst (Pi k)        = fromRational k * pi
    fromConst E             = exp 1
    fromConst (IntegerC x)  = fromInteger x
    fromConst (RationalC x) = x
#if defined(CYCLOTOMIC)
    fromConst (RealCycC x)   = RealCyc.toReal x
#endif /* defined(CYCLOTOMIC) */

    toConst = RationalC

instance RealFloat a => IsConst (Complex a) where
    fromConst (Const x)     = x
    fromConst (Pi k)        = fromRational k * pi
    fromConst E             = exp 1
    fromConst (IntegerC x)  = fromInteger x
    fromConst (RationalC x) = fromRational x
#if defined(CYCLOTOMIC)
    fromConst (RealCycC x)   = RealCyc.toReal x
    fromConst (CycC x)       = fromCyclotomic x
#endif /* defined(CYCLOTOMIC) */

-- | Lift a unary operation on @'Num'@ type class to the type @'Const' a@
liftNum :: (IsConst b, Num b)
        => (forall a . Num a => a -> a)
        -> Const b
        -> Const b
liftNum f (Const x)     = Const (f x)
liftNum f (IntegerC x)  = IntegerC (f x)
liftNum f (RationalC x) = RationalC (f x)
#if defined(CYCLOTOMIC)
liftNum f (RealCycC x)  = RealCycC (f x)
liftNum f (CycC x)      = CycC (f x)
#endif /* defined(CYCLOTOMIC) */
liftNum f x             = toConst (f (fromConst x))

-- | Lift a binary operation on @'Num'@ type class to the type @'Const' a@
liftNum2 :: (IsConst b, Num b)
         => (forall a . Num a => a -> a -> a)
         -> Const b
         -> Const b
         -> Const b
liftNum2 f (Const x)     (Const y)     = Const (f x y)
liftNum2 f (IntegerC x)  (IntegerC y)  = IntegerC (f x y)
liftNum2 f (RationalC x) (RationalC y) = RationalC (f x y)
#if defined(CYCLOTOMIC)
liftNum2 f (RealCycC x)  (RealCycC y)  = RealCycC (f x y)
liftNum2 f (CycC x)      (CycC y)      = CycC (f x y)
#endif /* defined(CYCLOTOMIC) */
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
    Pi k1 + Pi k2 = Pi (k1 + k2)
    x     + y     = liftNum2 (+) x y

    Pi k1 - Pi k2 = Pi (k1 - k2)
    x     - y     = liftNum2 (-) x y

    Pi k1        * IntegerC k2  = Pi (k1 * fromInteger k2)
    IntegerC k1  * Pi k2        = Pi (fromInteger k1 * k2)
    Pi k1        * RationalC k2 = Pi (k1 * k2)
    RationalC k1 * Pi k2        = Pi (k1 * k2)
    x            * y            = liftNum2 (*) x y

    negate (Pi k) = Pi (negate k)
    negate x      = liftNum negate x

    abs (Pi k) = Pi (abs k)
    abs x      = liftNum abs x

    signum (Pi k) = RationalC (signum k)
    signum x      = liftNum signum x

    fromInteger x = IntegerC x

instance (IsConst a, Real a) => Real (Const a) where
    toRational (Const x)     = toRational x
    toRational Pi{}          = error "can't happen"
    toRational E{}           = error "can't happen"
    toRational (IntegerC x)  = fromInteger x
    toRational (RationalC x) = x
#if defined(CYCLOTOMIC)
    toRational RealCycC{}    = error "can't happen"
    toRational CycC{}        = error "can't happen"
#endif /* defined(CYCLOTOMIC) */

instance Enum a => Enum (Const a) where
    toEnum x = Const (toEnum x)

    fromEnum (Const x)     = fromEnum x
    fromEnum Pi{}          = error "can't happen"
    fromEnum E{}           = error "can't happen"
    fromEnum (IntegerC x)  = fromEnum x
    fromEnum (RationalC x) = fromEnum x
#if defined(CYCLOTOMIC)
    fromEnum RealCycC{}    = error "can't happen"
    fromEnum CycC{}        = error "can't happen"
#endif /* defined(CYCLOTOMIC) */

instance (IsConst a, Integral a) => Integral (Const a) where
    quot = liftIntegral2 quot
    rem  = liftIntegral2 rem
    div  = liftIntegral2 div
    mod  = liftIntegral2 mod

    x `quotRem` y = (x `quot` y, x `rem` y)

    x `divMod` y = (x `div` y, x `mod` y)

    toInteger (Const x)    = toInteger x
    toInteger Pi{}         = error "can't happen"
    toInteger E{}          = error "can't happen"
    toInteger (IntegerC x) = x
    toInteger RationalC{}  = error "can't happen"
#if defined(CYCLOTOMIC)
    toInteger RealCycC{}   = error "can't happen"
    toInteger CycC{}       = error "can't happen"
#endif /* defined(CYCLOTOMIC) */

-- | Lift a unary operation on 'Num' to the type 'Const a'
liftFractional :: (IsConst b, Fractional b)
               => (forall a . Fractional a => a -> a)
               -> Const b
               -> Const b
liftFractional f (Const x)     = Const (f x)
liftFractional f (IntegerC x)  = RationalC (f (fromInteger x))
liftFractional f (RationalC x) = RationalC (f x)
#if defined(CYCLOTOMIC)
liftFractional f (RealCycC x)  = RealCycC (f x)
liftFractional f (CycC x)      = CycC (f x)
#endif /* defined(CYCLOTOMIC) */
liftFractional f x             = toConst (f (fromConst x))

-- | Lift a binary operation on 'Num' to the type 'Const a'
liftFractional2 :: (IsConst b, Fractional b)
                => (forall a . Fractional a => a -> a -> a)
                -> Const b
                -> Const b
                -> Const b
liftFractional2 f (Const x)     (Const y)     = Const (f x y)
liftFractional2 f (IntegerC x)  (IntegerC y)  = RationalC (f (fromInteger x) (fromInteger y))
liftFractional2 f (RationalC x) (RationalC y) = RationalC (f x y)
#if defined(CYCLOTOMIC)
liftFractional2 f (CycC x)      (CycC y)      = CycC (f x y)
liftFractional2 f (RealCycC x)  (RealCycC y)  = RealCycC (f x y)
#endif /* defined(CYCLOTOMIC) */
liftFractional2 f x             y             = joinWith (liftFractional2 f) x y

instance (IsConst a, Fractional a) => Fractional (Const a) where
    Pi x / IntegerC y  = Pi (x / fromInteger y)
    Pi x / RationalC y = Pi (x / y)
    x    / y           = liftFractional2 (/) x y

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
    pi = Pi 1

    exp = liftFloating exp

    log E = 1
    log x = liftFloating log x

#if defined(CYCLOTOMIC)
    sqrt (IntegerC x)  = RealCycC $ RealCyc.sqrtRat (fromInteger x)
    sqrt (RationalC x) = RealCycC $ RealCyc.sqrtRat x
#endif /* defined(CYCLOTOMIC) */
    sqrt x             = liftFloating sqrt x

    (**) = liftFloating2 (**)

#if defined(CYCLOTOMIC)
    sin (Pi k) = RealCycC (RealCyc.sinRev (k / 2))
#endif /* defined(CYCLOTOMIC) */
    sin x      = liftFloating sin x

#if defined(CYCLOTOMIC)
    cos (Pi k) = RealCycC (RealCyc.cosRev (k / 2))
#endif /* defined(CYCLOTOMIC) */
    cos x      = liftFloating cos x

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
    pi = Pi 1

    exp = liftFloating exp

    log E = 1
    log x = liftFloating log x

#if defined(CYCLOTOMIC)
    sqrt (IntegerC x)  = RealCycC $ RealCyc.sqrtRat (fromInteger x)
    sqrt (RationalC x) = RealCycC $ RealCyc.sqrtRat x
#endif /* defined(CYCLOTOMIC) */
    sqrt x             = liftFloating sqrt x

    (**) = liftFloating2 (**)

#if defined(CYCLOTOMIC)
    sin (Pi k) = RealCycC (RealCyc.sinRev (k / 2))
#endif /* defined(CYCLOTOMIC) */
    sin x      = liftFloating sin x

#if defined(CYCLOTOMIC)
    cos (Pi k) = RealCycC (RealCyc.cosRev (k / 2))
#endif /* defined(CYCLOTOMIC) */
    cos x      = liftFloating cos x

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
    pi = Pi 1

    exp = liftFloating exp

    log E = 1
    log x = liftFloating log x

#if defined(CYCLOTOMIC)
    sqrt (IntegerC x)  = CycC $ Cyc.sqrtInteger x
    sqrt (RationalC x) = CycC $ Cyc.sqrtRat x
#endif /* defined(CYCLOTOMIC) */
    sqrt x             = liftFloating sqrt x

    (**) = liftFloating2 (**)

#if defined(CYCLOTOMIC)
    sin (Pi k) = CycC (Cyc.sinRev (k / 2))
#endif /* defined(CYCLOTOMIC) */
    sin x      = liftFloating sin x

#if defined(CYCLOTOMIC)
    cos (Pi k) = CycC (Cyc.cosRev (k / 2))
#endif /* defined(CYCLOTOMIC) */
    cos x      = liftFloating cos x

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
    arbitrary = oneof [ Const <$> arbitrary
                      , IntegerC <$> arbitrary
                      , RationalC <$> arbitrary
                      ]

instance Arbitrary (Const Float) where
    arbitrary = frequency [ (10, Const <$> arbitrary)
                          , (1, pure E)
                          , (1, Pi <$> arbitrary)
                          , (10, IntegerC <$> arbitrary)
                          , (10, RationalC <$> arbitrary)
                          ]

instance Arbitrary (Const Double) where
    arbitrary = frequency [ (10, Const <$> arbitrary)
                          , (1, pure E)
                          , (1, Pi <$> arbitrary)
                          , (10, IntegerC <$> arbitrary)
                          , (10, RationalC <$> arbitrary)
                          ]

instance Arbitrary (Const (Complex Float)) where
    arbitrary = frequency [ (10, Const <$> arbitrary)
                          , (1, pure E)
                          , (1, Pi <$> arbitrary)
                          , (10, IntegerC <$> arbitrary)
                          , (10, RationalC <$> arbitrary)
                          ]

instance Arbitrary (Const (Complex Double)) where
    arbitrary = frequency [ (10, Const <$> arbitrary)
                          , (1, pure E)
                          , (1, Pi <$> arbitrary)
                          , (10, IntegerC <$> arbitrary)
                          , (10, RationalC <$> arbitrary)
                          ]

#if defined(CYCLOTOMIC)
instance Pretty Cyclotomic where
    pprPrec p (Cyclotomic n0 mp) =
        case Map.toList mp of
          []          -> "0"
          [(ex,rat)]  -> leadingTerm rat n0 ex
          (ex,rat):xs -> parensIf (p > addPrec) $
                         leadingTerm rat n0 ex <> mconcat (map (followingTerm n0) xs)
      where
        pprBaseExp :: Integer -> Integer -> Doc
        pprBaseExp n 1  = zeta <> text "_" <> ppr n
        pprBaseExp n ex = zeta <> text "_" <> ppr n <> text "^" <> ppr ex

        zeta :: Doc
        zeta = text "zeta"

        leadingTerm :: Rational -> Integer -> Integer -> Doc
        leadingTerm r _ 0 = ppr r
        leadingTerm r n ex
          | r == 1     = t
          | r == (-1)  = "-" <> t
          | r > 0      = ppr r <> t
          | r < 0      = "-" <> ppr (-r) <> t
          | otherwise  = mempty
          where
            t = pprBaseExp n ex

        followingTerm :: Integer -> (Integer, Rational) -> Doc
        followingTerm n (ex, r)
          | r == 1     = "+" <> t
          | r == (-1)  = "-" <> t
          | r > 0      = "+" <> ppr r <> t
          | r < 0      = "-" <> ppr (-r) <> t
          | otherwise  = mempty
          where
            t = pprBaseExp n ex

instance Pretty RealCyclotomic where
    pprPrec p (RealCyclotomic cyc) = pprPrec p cyc
#endif /* defined(CYCLOTOMIC) */

instance Pretty a => Pretty (Const a) where
    pprPrec p (Const x)     = pprPrec p x
    pprPrec p (Pi 0)        = pprPrec p (0 :: Integer)
    pprPrec _ (Pi 1)        = text "pi"
    pprPrec p (Pi k)        = parensIf (p > mulPrec) $
                              pprPrec mulPrec1 k <> char '*' <> text "pi"
    pprPrec _ E             = text "e"
    pprPrec p (IntegerC x)  = pprPrec p x
    pprPrec p (RationalC x) = parensIf (p > appPrec) $
                              text "fromRational" <+> pprPrec appPrec1 x
#if defined(CYCLOTOMIC)
    pprPrec p (RealCycC x)  = pprPrec p x
    pprPrec p (CycC x)      = pprPrec p x
#endif /* defined(CYCLOTOMIC) */

instance PrettyTeX a => PrettyTeX (Const a) where
    tppr (Const x)     = tppr x
    tppr (Pi 0)        = tppr (0 :: Integer)
    tppr (Pi 1)        = commS "pi"
    tppr (Pi k)        = tppr k <> commS "pi"
    tppr E             = comm1 "mathrm" "e"
    tppr (IntegerC x)  = tppr x
    tppr (RationalC x) = tppr x
#if defined(CYCLOTOMIC)
    tppr (RealCycC x)  = tppr x
    tppr (CycC x)      = tppr x
#endif /* defined(CYCLOTOMIC) */

instance PrettyTeX a => IHaskellDisplay (Const a) where
    display = displayMath
