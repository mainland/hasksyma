{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module      :  Hasksyma.Const
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu
--
-- Representations for exact, named, and evaluated constants.
--
-- Notebook display instances are provided separately by
-- "Hasksyma.IHaskell" in the public @hasksyma:ihaskell@ sublibrary.
-- QuickCheck instances are now test-only. Downstream tests that need
-- t'Const' generators must provide their own instances or explicit generators.

module Hasksyma.Const (
  Const(..),
  IsConst(..),
  isExact,
  sameConst,
  toRationalMaybe,
  toIntegerMaybe
) where

import           Data.Complex                    (Complex (..))
import           Data.Ratio                      (denominator, numerator)
#if defined(CYCLOTOMIC)
import           Data.Complex.Cyclotomic         (Cyclotomic (..))
import qualified Data.Complex.Cyclotomic         as Cyc
import qualified Data.Map                        as Map
import           Data.Maybe                      (fromJust)
import           Data.Number.RealCyclotomic      (RealCyclotomic (..))
import qualified Data.Number.RealCyclotomic      as RealCyc
#endif /* defined(CYCLOTOMIC) */
import           Text.LaTeX.Base.Class           (comm1, commS)
import           Text.PrettyPrint.Mainland       (char, parensIf, text, (<+>))
#if defined(CYCLOTOMIC)
import           Text.PrettyPrint.Mainland       (Doc)
#endif /* defined(CYCLOTOMIC) */
import           Text.PrettyPrint.Mainland.Class (Pretty (pprPrec))
#if defined(CYCLOTOMIC)
import           Text.PrettyPrint.Mainland.Class (Pretty (ppr))
#endif /* defined(CYCLOTOMIC) */
import           Hasksyma.LaTeX                  (PrettyTeX (tppr))
import           Hasksyma.Pretty                 (appPrec, appPrec1, mulPrec, mulPrec1)
#if defined(CYCLOTOMIC)
import           Hasksyma.Pretty                 (addPrec)
#endif /* defined(CYCLOTOMIC) */

-- | A symbolic constant whose evaluated values have type @a@.
--
-- Dedicated constructors represent exact integers, rationals, and named
-- constants without immediately converting them to @a@. The optional
-- @cyclotomic@ flag adds exact real and complex cyclotomic values.
--
-- With @cyclotomic@ enabled, 'abs' and 'signum' on exact cyclotomic constants
-- preserve exactness when the squared magnitude is rational, including zero
-- and real square roots of rationals. Other squared magnitudes currently raise
-- an error in the cyclotomic library. No approximate sign test is used.
--
-- Equality compares exact comparison keys, not rounded interpretations of
-- symbolic constants. Integers, rationals, zero multiples of pi, and rational
-- cyclotomic values share rational keys. Evaluated payloads participate through
-- 'exactRational', without changing whether 'isExact' reports them as exact.
-- Nonzero multiples of pi and Euler's number retain distinct symbolic keys.
-- This is a supported identity relation, not a general mathematical equality
-- decision procedure.
--
-- Ordering is structural, not numerical: rational keys precede nonzero pi
-- multiples, then Euler's number, nonrational cyclotomic keys when enabled,
-- and opaque payloads. Compare rational values and pi coefficients exactly,
-- and cyclotomic representations by their order and coefficient maps.
-- Project with 'fromConst' explicitly when numerical comparison is intended.
--
-- Opaque payloads inherit their underlying 'Eq' and 'Ord' behavior. The
-- instances are lawful when those payload instances are lawful. In particular,
-- floating NaNs remain nonreflexive and must not be used as ordered keys.
-- Signed floating zeros share a key. This is not bitwise IEEE identity.
--
-- Division by an exact zero and its reciprocal use the underlying @a@
-- operation. Floating payloads can therefore produce infinities or NaNs,
-- while rational payloads still raise their division-by-zero exception.
-- This also applies to negative integer powers of exact zero. Nonzero
-- rational division retains its exact representation.
--
-- Perfect squares stored as 'IntegerC' reduce to 'IntegerC' roots using
-- integer arithmetic, even beyond the floating payload's precision or range.
-- Square roots of negative real constants use the underlying floating
-- operation, including with @cyclotomic@ enabled. These arguments are never
-- passed to the exact real radical constructor.
-- Complex payloads retain principal complex square-root semantics.
--
-- Numeric projections are partial. 'toRational' accepts exact rational
-- representations, and 'toInteger' accepts exact integer representations.
-- 'fromEnum' delegates rational representations to their 'Enum' instance.
-- These operations reject unsupported symbolic constants instead of silently
-- approximating them. For @Const@ payloads they delegate to the underlying
-- type, inheriting its conversion behavior and possible exceptions.
-- Use 'toRationalMaybe' and 'toIntegerMaybe' for checked exact projections.
-- To request numerical evaluation explicitly, apply 'fromConst' first.
data Const a where
    -- | An already evaluated value.
    Const     :: a -> Const a
    -- | A rational multiple of pi.
    Pi        :: Floating a => Rational -> Const a
    -- | Euler's number.
    E         :: Floating a => Const a
    -- | An exact integer.
    IntegerC  :: Num a => Integer -> Const a
    -- | An exact rational number.
    RationalC :: Fractional a => Rational -> Const a
#if defined(CYCLOTOMIC)
    -- | An exact real cyclotomic value.
    RealCycC  :: RealFloat a => RealCyclotomic -> Const a
    -- | An exact complex cyclotomic value.
    CycC      :: RealFloat a => Cyclotomic -> Const (Complex a)
#endif /* defined(CYCLOTOMIC) */

-- | Convert between @a@ and @t'Const' a@.
class IsConst a where
    -- | Project a value of type @a@ from a @t'Const' a@.
    --
    -- The default implementation evaluates every constructor using its
    -- numeric constraints, so instances need only override this method to
    -- customize conversion.
    fromConst :: Const a -> a
    fromConst (Const x)     = x
    fromConst (Pi k)        = fromRational k * pi
    fromConst E             = exp 1
    fromConst (IntegerC x)  = fromInteger x
    fromConst (RationalC x) = fromRational x
#if defined(CYCLOTOMIC)
    fromConst (RealCycC x)  = RealCyc.toReal x
    fromConst (CycC x)      = fromCyclotomic x
#endif /* defined(CYCLOTOMIC) */

    -- | Construct a value of type @t'Const' a@ from a value of type @a@.
    toConst :: a -> Const a
    toConst x = Const x

    -- | Return the exact rational value of an evaluated payload when supported.
    -- Used for comparison and checked projection, without approximating
    -- symbolic constants or changing their stored representation.
    -- Return 'Nothing' for opaque values.
    -- A supplied rational must represent the payload exactly.
    --
    -- Built-in integral and rational instances provide their exact values.
    -- Finite floating values provide their exact binary rationals. Infinities,
    -- NaNs, and complex values with nonzero imaginary parts remain opaque.
    -- Custom instances default to opaque comparison, so their payloads remain
    -- distinct from exact constant constructors unless this method is supplied.
    exactRational :: a -> Maybe Rational
    exactRational _ = Nothing

    -- | Compare evaluated payloads for rewrite bookkeeping, not algebraic
    -- equality. The default uses '==' and inherits its limitations. Override
    -- it for payloads with nonreflexive equality if unbounded rewriting must
    -- recognize unchanged values.
    -- Reliable fixed-point and cycle detection require a reflexive, symmetric,
    -- transitive identity relation that distinguishes payload changes relevant
    -- to rewriting.
    --
    -- Built-in floating instances treat all NaNs as the same payload and
    -- distinguish signed zeros. Complex instances compare both components
    -- with that policy. This does not change ordinary 'Eq' or authorize
    -- algebraic identities involving NaNs. NaN bit patterns are not preserved
    -- by this identity relation.
    samePayload :: Eq a => a -> a -> Bool
    samePayload = (==)

-- | Compare constant constructors and their stored payloads for rewrite
-- bookkeeping. Unlike 'Eq', this distinguishes integer, rational, and
-- evaluated representations of the same value. Evaluated values use
-- 'samePayload', including its documented NaN and signed-zero policy.
-- This is not a mathematical equality test.
sameConst :: (Eq a, IsConst a) => Const a -> Const a -> Bool
sameConst (Const x)     (Const y)     = samePayload x y
sameConst (IntegerC x)  (IntegerC y)  = x == y
sameConst (RationalC x) (RationalC y) = x == y
sameConst (Pi x)        (Pi y)        = x == y
sameConst E             E             = True
#if defined(CYCLOTOMIC)
sameConst (RealCycC x)  (RealCycC y)  = x == y
sameConst (CycC x)      (CycC y)      = x == y
#endif
sameConst _             _             = False

-- | Return 'True' if a constant retains an exact symbolic representation.
--
-- >>> isExact (IntegerC 3 :: Const Double)
-- True
-- >>> isExact (Const 3 :: Const Double)
-- False
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

-- | Project a supported exact rational value without approximation.
--
-- Integer and rational constants, zero multiples of pi, and rational
-- cyclotomic constants are supported. Evaluated payloads use 'exactRational',
-- so finite built-in floating values yield their exact binary rationals.
-- Nonfinite or opaque payloads, nonreal complex values, and unsupported
-- irrational constants return 'Nothing'. This does not change 'isExact'.
toRationalMaybe :: IsConst a => Const a -> Maybe Rational
toRationalMaybe (Const x) = exactRational x
toRationalMaybe c         = symbolicRational c

-- | Project a supported exact integer value without rounding or truncation.
-- Return 'Nothing' when 'toRationalMaybe' fails or yields a noninteger.
toIntegerMaybe :: IsConst a => Const a -> Maybe Integer
toIntegerMaybe c = do
    q <- toRationalMaybe c
    if denominator q == 1 then Just (numerator q) else Nothing

-- Independent of the payload's IsConst instance, so Enum can project exact
-- symbolic values without strengthening its existing instance constraint.
symbolicRational :: Const a -> Maybe Rational
symbolicRational (IntegerC n)                  = Just (fromInteger n)
symbolicRational (RationalC q)                 = Just q
symbolicRational (Pi 0)                        = Just 0
#if defined(CYCLOTOMIC)
symbolicRational (RealCycC (RealCyclotomic x)) = Cyc.toRat x
symbolicRational (CycC x)                      = Cyc.toRat x
#endif
symbolicRational _                             = Nothing

-- Coerce constants to a common representation for arithmetic. The fallback
-- may approximate symbolic values, so comparison must not use this function.
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

-- Normalize only established exact equivalences. Constructor order gives a
-- structural order without requiring numerical ordering of named constants.
data ComparisonKey a
  = RationalKey Rational
  | PiKey Rational
  | EKey
#if defined(CYCLOTOMIC)
  | CyclotomicKey Integer [(Integer, Rational)]
#endif
  | PayloadKey a
  deriving (Eq, Ord)

comparisonKey :: IsConst a => Const a -> ComparisonKey a
comparisonKey (Const x)                     = maybe (PayloadKey x) RationalKey (exactRational x)
comparisonKey (IntegerC x)                  = RationalKey (fromInteger x)
comparisonKey (RationalC x)                 = RationalKey x
comparisonKey (Pi 0)                        = RationalKey 0
comparisonKey (Pi x)                        = PiKey x
comparisonKey E                             = EKey
#if defined(CYCLOTOMIC)
comparisonKey (RealCycC (RealCyclotomic x)) = cyclotomicKey x
comparisonKey (CycC x)                      = cyclotomicKey x

cyclotomicKey :: Cyclotomic -> ComparisonKey a
cyclotomicKey x = case Cyc.toRat x of
    Just q  -> RationalKey q
    Nothing -> CyclotomicKey (Cyc.order x) (Map.toAscList (Cyc.coeffs x))
#endif

instance (Eq a, IsConst a) => Eq (Const a) where
    x == y = comparisonKey x == comparisonKey y

instance (Ord a, IsConst a) => Ord (Const a) where
    compare x y = compare (comparisonKey x) (comparisonKey y)

#if defined(CYCLOTOMIC)
-- | Export a t'Cyclotomic' as an inexact complex number. This function avoids
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
    toConst = IntegerC . fromIntegral
    exactRational = Just . toRational

instance IsConst Integer where
    toConst = IntegerC
    exactRational = Just . fromInteger

instance IsConst Float where
    exactRational = finiteRational
    samePayload = sameFloatingPayload

instance IsConst Double where
    exactRational = finiteRational
    samePayload = sameFloatingPayload

instance IsConst Rational where
    toConst = RationalC
    exactRational = Just

instance RealFloat a => IsConst (Complex a) where
    exactRational (r :+ i) | i == 0 = finiteRational r
                           | otherwise = Nothing
    samePayload (r :+ i) (r' :+ i') =
        sameFloatingPayload r r' && sameFloatingPayload i i'

finiteRational :: RealFloat a => a -> Maybe Rational
finiteRational x | isNaN x || isInfinite x = Nothing
                 | otherwise = Just (toRational x)

sameFloatingPayload :: RealFloat a => a -> a -> Bool
sameFloatingPayload x y
    | isNaN x && isNaN y = True
    | x == 0 && y == 0   = isNegativeZero x == isNegativeZero y
    | otherwise          = x == y

-- | Lift a unary operation on @'Num'@ type class to the type @t'Const' a@.
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

-- | Lift a binary operation on @'Num'@ type class to the type @t'Const' a@.
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

-- | Lift a binary operation on 'Integral' to the type @t'Const' b@.
liftIntegral2 :: (IsConst b, Integral b)
              => (forall a . Integral a => a -> a -> a)
              -> Const b
              -> Const b
              -> Const b
liftIntegral2 f (Const x)    (Const y)    = Const (f x y)
liftIntegral2 f (IntegerC x) (IntegerC y) = IntegerC (f x y)
liftIntegral2 f x            y            = joinWith (liftIntegral2 f) x y

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

    abs (Pi k)                        = Pi (abs k)
#if defined(CYCLOTOMIC)
    -- The real wrapper leaves abs and signum undefined. Use the exact complex
    -- implementation, which supports rational squared magnitudes.
    abs (RealCycC (RealCyclotomic x)) = RealCycC (RealCyclotomic (abs x))
#endif
    abs x                             = liftNum abs x

    signum (Pi k)                        = RationalC (signum k)
#if defined(CYCLOTOMIC)
    signum (RealCycC (RealCyclotomic x)) = RealCycC (RealCyclotomic (signum x))
#endif
    signum x                             = liftNum signum x

    fromInteger x = IntegerC x

instance (IsConst a, Real a) => Real (Const a) where
    toRational (Const x) = toRational x
    toRational c         = case symbolicRational c of
                             Just q  -> q
                             Nothing -> error "toRational: constant has no supported exact rational projection"

instance Enum a => Enum (Const a) where
    toEnum x = Const (toEnum x)

    fromEnum (Const x)     = fromEnum x
    fromEnum (IntegerC x)  = fromEnum x
    fromEnum (RationalC x) = fromEnum x
    fromEnum c             = case symbolicRational c of
                               Just q  -> fromEnum q
                               Nothing -> error "fromEnum: constant requires explicit evaluation"

instance (IsConst a, Integral a) => Integral (Const a) where
    quot = liftIntegral2 quot
    rem  = liftIntegral2 rem
    div  = liftIntegral2 div
    mod  = liftIntegral2 mod

    x `quotRem` y = (x `quot` y, x `rem` y)

    x `divMod` y = (x `div` y, x `mod` y)

    toInteger (Const x)    = toInteger x
    toInteger (IntegerC x) = x
    toInteger c            = case toIntegerMaybe c of
                               Just n  -> n
                               Nothing -> error "toInteger: constant has no supported exact integer projection"

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

-- Exact arithmetic cannot represent division by zero. Recognize it without
-- requiring Eq for arbitrary payloads or approximating symbolic constants.
isExactZero :: Const a -> Bool
isExactZero (IntegerC x)  = x == 0
isExactZero (RationalC x) = x == 0
isExactZero (Pi x)        = x == 0
#if defined(CYCLOTOMIC)
isExactZero (RealCycC x)  = x == 0
isExactZero (CycC x)      = x == 0
#endif
isExactZero _             = False

instance (IsConst a, Fractional a) => Fractional (Const a) where
    x / y | isExactZero y = toConst (fromConst x / fromConst y)

    Pi x / IntegerC y  = Pi (x / fromInteger y)
    Pi x / RationalC y = Pi (x / y)
    x    / y           = liftFractional2 (/) x y

    recip x | isExactZero x = toConst (recip (fromConst x))
    recip x                 = liftFractional recip x

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

-- Recognize a nonnegative perfect square without a floating approximation.
exactIntegerSqrt :: Integer -> Maybe Integer
exactIntegerSqrt n
    | n < 0     = Nothing
    | n == 0    = Just 0
    | r*r == n  = Just r
    | otherwise = Nothing
  where
    r = go n

    -- Integer Newton iteration starts above the root. Estimates stay positive
    -- and never fall below the floor of the root, so division is safe. Stop
    -- when the estimate no longer decreases to avoid cycling for nonsquares.
    go x
        | y >= x    = x
        | otherwise = go y
      where
        y = (x + n `quot` x) `quot` 2

instance Floating (Const Float) where
    pi = Pi 1

    exp = liftFloating exp

    log E = 1
    log x = liftFloating log x

    sqrt (IntegerC x) | Just y <- exactIntegerSqrt x = IntegerC y
#if defined(CYCLOTOMIC)
    sqrt (IntegerC x)  | x >= 0 = RealCycC $ RealCyc.sqrtRat (fromInteger x)
    sqrt (RationalC x) | x >= 0 = RealCycC $ RealCyc.sqrtRat x
#endif /* defined(CYCLOTOMIC) */
    sqrt x             = liftFloating sqrt x

    IntegerC m ** IntegerC n | m /= 0 = RationalC (fromInteger m ^^ n)
    x ** y                            = liftFloating2 (**) x y

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

    sqrt (IntegerC x) | Just y <- exactIntegerSqrt x = IntegerC y
#if defined(CYCLOTOMIC)
    sqrt (IntegerC x)  | x >= 0 = RealCycC $ RealCyc.sqrtRat (fromInteger x)
    sqrt (RationalC x) | x >= 0 = RealCycC $ RealCyc.sqrtRat x
#endif /* defined(CYCLOTOMIC) */
    sqrt x             = liftFloating sqrt x

    IntegerC m ** IntegerC n | m /= 0 = RationalC (fromInteger m ^^ n)
    x ** y                            = liftFloating2 (**) x y

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

    sqrt (IntegerC x) | Just y <- exactIntegerSqrt x = IntegerC y
#if defined(CYCLOTOMIC)
    sqrt (IntegerC x)  = CycC $ Cyc.sqrtInteger x
    sqrt (RationalC x) = CycC $ Cyc.sqrtRat x
#endif /* defined(CYCLOTOMIC) */
    sqrt x             = liftFloating sqrt x

    IntegerC m ** IntegerC n | m /= 0 = RationalC (fromInteger m ^^ n)
    x ** y                            = liftFloating2 (**) x y

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
