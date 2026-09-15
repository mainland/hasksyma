{-# LANGUAGE CPP                        #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE UndecidableInstances       #-}

-- |
-- Module      :  Hasksyma.Exp
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu
--
-- The typed expression tree and the numeric instances used to construct it.
--
-- Notebook display instances are provided separately by "Hasksyma.IHaskell"
-- in the public @hasksyma:ihaskell@ sublibrary. Import that module to enable them.

module Hasksyma.Exp (
  Var(..),
  Exp(..),
  NumUnop(..),
  FracUnop(..),
  FloatUnop(..),
  NumBinop(..),
  IntBinop(..),
  FracBinop(..),
  FloatBinop(..),

  isConstE,
  isExactE,

  numunop,
  fracunop,
  floatunop,
  numbinop,
  intbinop,
  fracbinop,
  floatbinop,

  liftNum,
  liftNum2,
  liftIntegral2,
  liftFractional,
  liftFractional2,
  liftFloating,
  liftFloating2,
  liftNatPow,
  liftIntPow,
  liftFracPow
) where

import           Data.Ratio                      (denominator, numerator)
import           Data.Symbol                     (Symbol, unintern)
import           Numeric.Natural                 (Natural)
import           Text.LaTeX                      (IsString (..), autoBrackets, operatorname, tsqrt,
                                                  (!:), (^:))
import           Text.LaTeX.Base.Class           (LaTeXC, braces, comm1, commS)
import           Text.LaTeX.Base.Math            (frac, integral, integralFromTo)
import           Text.PrettyPrint.Mainland       (Doc, char, parensIf, text, (<+/>), (<+>))
import           Text.PrettyPrint.Mainland.Class (Pretty (ppr, pprPrec))

import           Hasksyma.Const                  (Const (..), IsConst, isExact)
import           Hasksyma.LaTeX                  (PrettyTeX (tppr, tpprPrec), autoParensIf, mathrel,
                                                  tinfixop)
import           Hasksyma.Pretty                 (Fixity, HasFixity (..), addPrec, addPrec1,
                                                  appPrec, appPrec1, infixl_, infixop, infixr_,
                                                  mulPrec, mulPrec1, negPrec, negPrec1, powPrec,
                                                  powPrec1)

-- | The name of a symbolic variable.
--
-- With @OverloadedStrings@, string literals can be used wherever a t'Var' is
-- expected.
newtype Var = Var Symbol
  deriving (Eq, Show, IsString)

instance Ord Var where
    compare (Var x) (Var y) = compare (unintern x) (unintern y)

-- | Num unary operators
data NumUnop = Neg
             | Abs
             | Signum
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Fractional unary operators
data FracUnop = Recip
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Floating unary operators
data FloatUnop = Exp
               | Log
               | Sqrt
               | Sin
               | Cos
               | Tan
               | Asin
               | Acos
               | Atan
               | Sinh
               | Cosh
               | Tanh
               | Asinh
               | Acosh
               | Atanh
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Num binary operators
data NumBinop = Add
              | Sub
              | Mul
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Integral binary operators
data IntBinop = Quot
              | Rem
              | Div
              | Mod
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Fractional binary operators
data FracBinop = FDiv
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Floating binary operators
data FloatBinop = Pow
                | Root
                | LogBase
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | A typed symbolic expression.
--
-- The parameter @a@ is the type used when constants are evaluated. Numeric
-- instances let ordinary Haskell operators construct expression trees.
-- Operator constructors carry the numeric constraints needed to interpret
-- them. 'NatPowE' stores a 'Natural' exponent, while 'IntPowE' supports
-- negative 'Integer' exponents and requires 'Fractional'. 'FracPowE' stores
-- an exact 'Rational' exponent and uses 'Floating' exponentiation.
--
-- Migration: replace the former nonnegative @IntPowE e n@ with
-- @NatPowE e (fromInteger n)@ after checking @n >= 0@. Rename the former
-- signed @FracPowE e n@ to @IntPowE e n@. Apply the same changes to
-- @liftIntPow@ and @liftFracPow@ calls. The new rational-power constructor
-- requires 'Floating', so it is not a replacement for signed powers over
-- 'Rational'. Derived 'Show' and 'Ord' results reflect the new constructors.
data Exp a where
    -- | An undefined value.
    Undefined   :: Exp a
    -- | Positive infinity.
    Infty       :: Exp a
    -- | Negative infinity.
    NegInfty    :: Exp a
    -- | A constant value.
    ConstE      :: Const a -> Exp a
    -- | A symbolic variable.
    VarE        :: Var -> Exp a
    -- | A unary operation from 'Num'.
    NumUnopE    :: Num a => NumUnop -> Exp a -> Exp a
    -- | A unary operation from 'Fractional'.
    FracUnopE   :: Fractional a => FracUnop -> Exp a -> Exp a
    -- | A unary operation from 'Floating'.
    FloatUnopE  :: (Floating a, Floating (Const a)) => FloatUnop -> Exp a -> Exp a
    -- | A binary operation from 'Num'.
    NumBinopE   :: Num a => NumBinop -> Exp a -> Exp a -> Exp a
    -- | Exponentiation by a nonnegative exponent in a 'Num' expression.
    -- Use 'IntPowE' when the exponent may be negative.
    NatPowE     :: Num a => Exp a -> Natural -> Exp a
    -- | Exponentiation by a signed integral exponent.
    IntPowE     :: Fractional a => Exp a -> Integer -> Exp a
    -- | Exponentiation by an exact rational exponent, interpreted using
    -- @(**)@. This retains the underlying type's behavior for negative and
    -- complex bases, rather than selecting a real root for odd denominators.
    FracPowE    :: (Floating a, Floating (Const a)) => Exp a -> Rational -> Exp a
    -- | A binary operation from 'Integral'.
    IntBinopE   :: Integral a => IntBinop -> Exp a -> Exp a -> Exp a
    -- | Division from 'Fractional'.
    FracBinopE  :: Fractional a => FracBinop -> Exp a -> Exp a -> Exp a
    -- | A binary operation from 'Floating'.
    FloatBinopE :: (Floating a, Floating (Const a)) => FloatBinop -> Exp a -> Exp a -> Exp a
    -- | An unevaluated derivative with respect to a variable.
    DiffE       :: (Floating a, Floating (Const a)) => Exp a -> Var -> Exp a
    -- | An indefinite or definite integral with respect to a variable.
    --
    -- 'Nothing' represents an indefinite integral. @'Just' (lower, upper)@
    -- represents a definite integral.
    IntE        :: (Floating a, Floating (Const a)) => Maybe (Exp a, Exp a) -> Exp a -> Var -> Exp a

-- | Return 'True' if an expression is a single constant node.
--
-- >>> import Hasksyma.Const (Const (..))
-- >>> isConstE (ConstE (IntegerC 3) :: Exp Double)
-- True
-- >>> isConstE (Undefined :: Exp Double)
-- False
isConstE :: Exp a -> Bool
isConstE ConstE{} = True
isConstE _        = False

-- | Return 'True' if every part of an expression has an exact symbolic
-- representation.
--
-- >>> import Hasksyma.Const (Const (..))
-- >>> isExactE (VarE "x" :: Exp Double)
-- True
-- >>> isExactE (ConstE (Const pi) :: Exp Double)
-- False
isExactE :: Exp a -> Bool
isExactE Undefined{}              = True
isExactE Infty{}                  = True
isExactE NegInfty{}               = True
isExactE (ConstE c)               = isExact c
isExactE VarE{}                   = True
isExactE (NumUnopE _ e)           = isExactE e
isExactE (FracUnopE _ e)          = isExactE e
isExactE (FloatUnopE _ e)         = isExactE e
isExactE (NumBinopE _ e1 e2)      = isExactE e1 && isExactE e2
isExactE (NatPowE e _)            = isExactE e
isExactE (IntPowE e _)            = isExactE e
isExactE (FracPowE e _)           = isExactE e
isExactE (IntBinopE _ e1 e2)      = isExactE e1 && isExactE e2
isExactE (FracBinopE _ e1 e2)     = isExactE e1 && isExactE e2
isExactE (FloatBinopE _ e1 e2)    = isExactE e1 && isExactE e2
isExactE (DiffE e _)              = isExactE e
isExactE (IntE Nothing e _)       = isExactE e
isExactE (IntE (Just (l, u)) e _) = isExactE l && isExactE u && isExactE e

-- | Compute function corresponding 'NumUnop' operator
numunop :: NumUnop -> (forall a . Num a => a -> a)
numunop Neg    = negate
numunop Abs    = abs
numunop Signum = signum

-- | Compute function corresponding 'FracUnop' operator
fracunop :: FracUnop -> (forall a . Fractional a => a -> a)
fracunop Recip = recip

-- | Compute function corresponding 'FloatUnop' operator
floatunop :: FloatUnop -> (forall a . Floating a => a -> a)
floatunop Exp   = exp
floatunop Log   = log
floatunop Sqrt  = sqrt
floatunop Sin   = sin
floatunop Cos   = cos
floatunop Tan   = tan
floatunop Asin  = asin
floatunop Acos  = acos
floatunop Atan  = atan
floatunop Sinh  = sinh
floatunop Cosh  = cosh
floatunop Tanh  = tanh
floatunop Asinh = asinh
floatunop Acosh = acosh
floatunop Atanh = atanh

-- | Compute function corresponding 'NumBinop' operator
numbinop :: NumBinop -> (forall a . Num a => a -> a -> a)
numbinop Add = (+)
numbinop Sub = (-)
numbinop Mul = (*)

-- | Compute function corresponding 'IntBinop' operator
intbinop :: IntBinop -> (forall a . Integral a => a -> a -> a)
intbinop Quot = quot
intbinop Rem  = rem
intbinop Div  = div
intbinop Mod  = mod

-- | Compute function corresponding 'FracBinop' operator
fracbinop :: FracBinop -> (forall a . Fractional a => a -> a -> a)
fracbinop FDiv = (/)

-- | Compute function corresponding 'floatbinop' operator
floatbinop :: FloatBinop -> (forall a . Floating a => a -> a -> a)
floatbinop Pow     = (**)
floatbinop Root    = \t u -> t ** recip u
floatbinop LogBase = logBase

-- | Lift a 'NumUnop' operator to an @t'Exp' a@, reducing constants when possible
-- while preserving exactness.
liftNum :: (IsConst a, Num a)
        => NumUnop
        -> Exp a
        -> Exp a
liftNum op (ConstE x) | isExact y = ConstE y
  where
    y = numunop op x

liftNum op e = NumUnopE op e

-- | Lift a 'NumBinop' operator to an @t'Exp' a@, reducing constants when possible
-- while preserving exactness.
liftNum2 :: (IsConst a, Num a)
         => NumBinop
         -> Exp a
         -> Exp a
         -> Exp a
liftNum2 op (ConstE x) (ConstE y) | isExact z = ConstE z
  where
    z = numbinop op x y

liftNum2 op e1 e2 = NumBinopE op e1 e2

-- | Lift a 'IntBinop' operator to an @t'Exp' a@, reducing constants when
-- possible while preserving exactness.
liftIntegral2 :: (IsConst a, Integral a)
              => IntBinop
              -> Exp a
              -> Exp a
              -> Exp a
liftIntegral2 op (ConstE x) (ConstE y) | isExact z = ConstE z
  where
    z = intbinop op x y

liftIntegral2 op e1 e2 = IntBinopE op e1 e2

-- | Lift a 'FracUnop' operator to an @t'Exp' a@, reducing constants when
-- possible while preserving exactness.
liftFractional :: (IsConst a, Fractional a, Eq a)
               => FracUnop
               -> Exp a
               -> Exp a
liftFractional op (ConstE x) | (not (isRecip op) || x /= 0) && isExact y = ConstE y
  where
    y = fracunop op x

    isRecip :: FracUnop -> Bool
    isRecip Recip = True

liftFractional op e = FracUnopE op e

-- | Lift a 'FracBinop' operator to an @t'Exp' a@, reducing constants when
-- possible while preserving exactness.
liftFractional2 :: (IsConst a, Eq a, Fractional a)
                => FracBinop
                -> Exp a
                -> Exp a
                -> Exp a
liftFractional2 op (ConstE x) (ConstE y) | (not (isFDiv op) || y /= 0) && isExact z = ConstE z
  where
    z = fracbinop op x y

    isFDiv :: FracBinop -> Bool
    isFDiv FDiv = True

liftFractional2 op e1 e2 = FracBinopE op e1 e2

-- | Lift a 'FloatUnop' operator to an @t'Exp' a@, reducing constants when
-- possible while preserving exactness.
liftFloating :: (IsConst a, Floating a, Floating (Const a))
             => FloatUnop
             -> Exp a
             -> Exp a
liftFloating op (ConstE x) | isExact y = ConstE y
  where
    y = floatunop op x

liftFloating op e = FloatUnopE op e

-- | Lift a 'FloatBinop' operator to an @t'Exp' a@, reducing constants when
-- possible while preserving exactness.
liftFloating2 :: (IsConst a, Floating a, Floating (Const a))
              => FloatBinop
              -> Exp a
              -> Exp a
              -> Exp a
liftFloating2 LogBase (ConstE (IntegerC x)) (ConstE (IntegerC y)) | x ^ z == y = ConstE (IntegerC z)
  where
    z :: Integer
    z = round (logBase (fromIntegral x) (fromIntegral y) :: Double)

liftFloating2 op (ConstE x) (ConstE y) | isExact z = ConstE z
  where
    z = floatbinop op x y

liftFloating2 op e1 e2 = FloatBinopE op e1 e2

-- | Lift raising a number to a nonnegative integral power to an @t'Exp' a@,
-- reducing constants when possible while preserving exactness.
liftNatPow :: (IsConst a, Num a, Eq a)
           => Exp a
           -> Natural
           -> Exp a
liftNatPow (ConstE x) n | (x /= 0 || n /= 0) && isExact z = ConstE z
  where
    z = x ^ n

liftNatPow e n = NatPowE e n

-- | Lift operation of raising a number to an integral power to an
-- @t'Exp' a@, reducing constants when possible while preserving exactness.
liftIntPow :: (IsConst a, Fractional a, Eq a)
           => Exp a
           -> Integer
           -> Exp a
liftIntPow (ConstE x) n | (x /= 0 || n > 0) && isExact z = ConstE z
  where
    z = x ^^ n

liftIntPow e n = IntPowE e n

-- | Lift exponentiation by an exact rational exponent, reducing constants
-- only when the result retains an exact representation. Integral exponents
-- are delegated to 'liftIntPow'.
liftFracPow :: (IsConst a, Floating a, Floating (Const a), Eq a)
            => Exp a
            -> Rational
            -> Exp a
liftFracPow e n | denominator n == 1 = liftIntPow e (numerator n)
liftFracPow (ConstE x) n | isExact z = ConstE z
  where
    z = x ** fromRational n

liftFracPow e n = FracPowE e n

deriving instance Show a => Show (Exp a)
deriving instance (Eq a, IsConst a) => Eq (Exp a)
deriving instance (Ord a, IsConst a) => Ord (Exp a)

instance (Num a, IsConst a, Eq (Exp a)) => Num (Exp a) where
#if defined(PEVAL)
    e1 + e2
      | e1 == 0   = e2
      | e2 == 0   = e1
      | otherwise = liftNum2 Add e1 e2

    e1 - e2
      | e1 == 0   = -e2
      | e2 == 0   = e1
      | otherwise = liftNum2 Sub e1 e2

    NatPowE e n * e'
      | e' == e  = NatPowE e (n+1)

    e * NatPowE e' n
      | e' == e  = NatPowE e (n+1)

    NatPowE e n * NatPowE e' m
      | e' == e  = NatPowE e (n+m)

    e1 * e2
      | e1 == 0   = 0
      | e2 == 0   = 0
      | e1 == 1   = e2
      | e2 == 1   = e1
      | e1 == e2  = NatPowE e1 2
      | otherwise = liftNum2 Mul e1 e2
#else /* !defined(PEVAL) */
    e1 + e2 = NumBinopE Add e1 e2
    e1 - e2 = NumBinopE Sub e1 e2
    e1 * e2 = NumBinopE Mul e1 e2
#endif /* !defined(PEVAL) */

    abs = NumUnopE Abs

    negate = NumUnopE Neg

    signum = NumUnopE Signum

    fromInteger = ConstE . fromInteger

instance Enum a => Enum (Exp a) where
    toEnum x = ConstE (toEnum x)

    fromEnum (ConstE x) = fromEnum x
    fromEnum _          = error "cannot convert expression to Int"

instance (Num a, IsConst a, Real (Const a), Ord (Exp a)) => Real (Exp a) where
    toRational (ConstE x) = toRational x
    toRational _          = error "cannot convert expression to Rational"

instance (IsConst a, Integral a) => Integral (Exp a) where
    quot = IntBinopE Quot
    rem  = IntBinopE Rem
    div  = IntBinopE Div
    mod  = IntBinopE Mod

    x `quotRem` y = (x `quot` y, x `rem` y)

    x `divMod` y = (x `div` y, x `mod` y)

    toInteger (ConstE x) = toInteger x
    toInteger _          = error "cannot convert expression to Integer"

instance (Fractional a, Eq a, IsConst a) => Fractional (Exp a) where
#if defined(PEVAL)
    (/) = liftFractional2 FDiv

    recip e@VarE{}      = IntPowE e (-1)
    recip (NatPowE e n) = IntPowE e (negate (toInteger n))
    recip e             = FracUnopE Recip e
#else /* !defined(PEVAL) */
    (/) = FracBinopE FDiv

    recip = FracUnopE Recip
#endif /* !defined(PEVAL) */

    fromRational = ConstE . fromRational

instance (Floating a, Eq a, IsConst a, Floating (Const a)) => Floating (Exp a) where
    pi = ConstE pi

#if defined(PEVAL)
    exp = liftFloating Exp

    log = liftFloating Log

    sqrt = liftFloating Sqrt

    e1 ** e2
        | e2 == 0 && e1 /= 0 = 1
        | e2 == 1            = e1
        | ConstE (IntegerC n) <- e2 = liftIntPow e1 n
        | ConstE (RationalC n) <- e2 = liftFracPow e1 n
        | otherwise = FloatBinopE Pow e1 e2
#else /* !defined(PEVAL) */
    exp = FloatUnopE Exp

    log = FloatUnopE Log

    sqrt = FloatUnopE Sqrt

    (**) = FloatBinopE Pow
#endif /* !defined(PEVAL) */

    logBase = FloatBinopE LogBase

    sin = FloatUnopE Sin
    cos = FloatUnopE Cos
    tan = FloatUnopE Tan

    asin = FloatUnopE Asin
    acos = FloatUnopE Acos
    atan = FloatUnopE Atan

    sinh = FloatUnopE Sinh
    cosh = FloatUnopE Cosh
    tanh = FloatUnopE Tanh

    asinh = FloatUnopE Asinh
    acosh = FloatUnopE Acosh
    atanh = FloatUnopE Atanh

instance Pretty Var where
    ppr (Var sym) = fromString (unintern sym)

instance PrettyTeX Var where
    tppr (Var sym) = fromString (unintern sym)

instance HasFixity NumBinop where
    fixity Add = infixl_ 6
    fixity Sub = infixl_ 6
    fixity Mul = infixl_ 7

instance HasFixity IntBinop where
    fixity Quot = infixl_ 7
    fixity Rem  = infixl_ 7
    fixity Div  = infixl_ 7
    fixity Mod  = infixl_ 7

instance HasFixity FracBinop where
    fixity FDiv = infixl_ 7

instance HasFixity FloatBinop where
    fixity Pow     = infixr_ 8
    fixity Root    = infixr_ 8
    fixity LogBase = infixr_ 10

instance Pretty NumUnop where
    ppr Neg    = "-"
    ppr Abs    = "abs"
    ppr Signum = "signum"

instance Pretty FracUnop where
    ppr Recip  = "recip"

instance Pretty FloatUnop where
    ppr Exp   = "exp"
    ppr Log   = "log"
    ppr Sqrt  = "sqrt"
    ppr Sin   = "sin"
    ppr Cos   = "cos"
    ppr Tan   = "tan"
    ppr Asin  = "asin"
    ppr Acos  = "acos"
    ppr Atan  = "atan"
    ppr Sinh  = "sinh"
    ppr Cosh  = "cosh"
    ppr Tanh  = "tanh"
    ppr Asinh = "asinh"
    ppr Acosh = "acosh"
    ppr Atanh = "atanh"

instance Pretty NumBinop where
    ppr Add = "+"
    ppr Sub = "-"
    ppr Mul = "*"

instance Pretty IntBinop where
    ppr Quot = "`quot`"
    ppr Rem  = "`rem`"
    ppr Div  = "`div`"
    ppr Mod  = "`mod`"

instance Pretty FracBinop where
    ppr FDiv = "/"

instance Pretty FloatBinop where
    ppr Pow     = "**"
    ppr Root    = "root"
    ppr LogBase = "logBase"

-- | Pretty print application of a unary function
unapp :: (Pretty a, Pretty b) => Int -> a -> b -> Doc
unapp p f e = parensIf (p > appPrec) $
              ppr f <+> pprPrec appPrec1 e

instance (Pretty a, Num a, IsConst a, Eq a) => Pretty (Exp a) where
    pprPrec _ Undefined  = "Undefined"
    pprPrec _ Infty      = "Infty"
    pprPrec _ NegInfty   = "-Infty"
    pprPrec p (ConstE c) = pprPrec p c
    pprPrec p (VarE v)   = pprPrec p v

    pprPrec p (NumUnopE Neg e)  = parensIf (p > negPrec1) $
                                  char '-' <> pprPrec negPrec e
    pprPrec p (NumUnopE op e)   = unapp p op e
    pprPrec p (FracUnopE op e)  = unapp p op e
    pprPrec p (FloatUnopE op e) = unapp p op e

    pprPrec p (NumBinopE op e1 e2)  = infixop p op e1 e2
    pprPrec p (NatPowE e n)         = parensIf (p > powPrec) $
                                      pprPrec powPrec1 e <+> text "^" <+/> pprPrec powPrec (toInteger n)
    pprPrec p (IntPowE e n)         = parensIf (p > powPrec) $
                                      pprPrec powPrec1 e <+> text "^^" <+/> pprPrec powPrec n
    pprPrec p (FracPowE e n)        = parensIf (p > powPrec) $
                                      pprPrec powPrec1 e <+> text "**" <+/> pprPrec powPrec n
    pprPrec p (IntBinopE op e1 e2)  = infixop p op e1 e2
    pprPrec p (FracBinopE op e1 e2) = infixop p op e1 e2

    pprPrec p (FloatBinopE Root e1 e2) =
        infixop p Pow e2 (recip e1)

    pprPrec p (FloatBinopE LogBase e1 e2) =
        parensIf (p > appPrec) $
        text "logBase" <+> pprPrec appPrec1 e1 <+> pprPrec appPrec1 e2

    pprPrec p (FloatBinopE op e1 e2) =
        infixop p op e1 e2

    pprPrec p (DiffE e x) =
        parensIf (p > appPrec) $
        text "diff" <+> pprPrec appPrec1 e <+> pprPrec appPrec1 x

    pprPrec p (IntE Nothing e x) =
        parensIf (p > appPrec) $
        text "integrate" <+> pprPrec appPrec1 e <+> pprPrec appPrec1 x

    pprPrec p (IntE (Just (l, u)) e x) =
        parensIf (p > appPrec) $
        text "dintegrate" <+> pprPrec appPrec1 l <+> pprPrec appPrec1 u <+> pprPrec appPrec1 e <+> pprPrec appPrec1 x

instance (PrettyTeX a, Num a, Eq a, IsConst a) => PrettyTeX (Exp a) where
    tpprPrec _ Undefined  = commS "bot"
    tpprPrec _ Infty      = commS "infty"
    tpprPrec _ NegInfty   = - (commS "infty")
    tpprPrec p (ConstE c) = tpprPrec p c
    tpprPrec p (VarE v)   = tpprPrec p v

    tpprPrec p (NumUnopE Neg e) =
        autoParensIf (p > negPrec1) $
        "-" <> tpprPrec negPrec e

    tpprPrec _ (NumUnopE Abs e) =
        autoBrackets "|" "|" (tppr e)

    tpprPrec p (NumUnopE op e) =
        autoParensIf (p > appPrec) $
        top op $ tpprPrec appPrec1 e
      where
        top :: LaTeXC l => NumUnop -> l -> l
        top Neg    _ = error "can't happen"
        top Abs    _ = error "can't happen"
        top Signum x = operatorname "sgn" <> x

    tpprPrec _ (FracUnopE Recip e) =
        frac 1 (tppr e)

    tpprPrec _ (FloatUnopE Sqrt e) =
        tsqrt Nothing (tppr e)

    tpprPrec p (FloatUnopE op e) =
        autoParensIf (p > appPrec) $
        top op $ tpprPrec appPrec1 e
      where
        top :: LaTeXC l => FloatUnop -> l -> l
        top Exp   = comm1 "exp"
        top Log   = comm1 "log"
        top Sqrt  = error "can't happen"
        top Sin   = comm1 "sin"
        top Cos   = comm1 "cos"
        top Tan   = comm1 "tan"
        top Asin  = comm1 "arcsin"
        top Acos  = comm1 "arccos"
        top Atan  = comm1 "arctan"
        top Sinh  = comm1 "sinh"
        top Cosh  = comm1 "cosh"
        top Tanh  = comm1 "tanh"
        top Asinh = comm1 "sinh^{-1}"
        top Acosh = comm1 "cosh^{-1}"
        top Atanh = comm1 "tanh^{-1}"

    tpprPrec p (NumBinopE Mul e1 e2) | not (isConstE e2) =
        autoParensIf (p > mulPrec) $
        tpprPrec mulPrec e1 <> tpprPrec mulPrec1 e2

    tpprPrec p (NumBinopE op e1 e2) =
        tinfixop p (fixity op) (top op) e1 e2
      where
        top :: LaTeXC l => NumBinop -> l
        top Add = "+"
        top Sub = "-"
        top Mul = commS "cdot"

    tpprPrec p (NatPowE e n) =
        autoParensIf (p > powPrec) $
        tpprPrec appPrec1 e ^: tpprPrec powPrec (toInteger n)

    tpprPrec p (IntPowE e n) =
        autoParensIf (p > powPrec) $
        tpprPrec appPrec1 e ^: tpprPrec powPrec n

    tpprPrec p (FracPowE e n) =
        autoParensIf (p > powPrec) $
        tpprPrec appPrec1 e ^: tpprPrec powPrec n

    tpprPrec p (IntBinopE op e1 e2) =
        tinfixop p (fixity op) (top op) e1 e2
      where
        top :: LaTeXC l => IntBinop -> l
        top Quot = mathrel (operatorname "quot")
        top Rem  = mathrel (operatorname "rem")
        top Div  = mathrel (operatorname "div")
        top Mod  = commS "bmod"

    tpprPrec p (FracBinopE op e1 e2) =
        tinfixop p (tfixity op) (top op) e1 e2
      where
        tfixity :: FracBinop -> Fixity
        tfixity FDiv = infixl_ 7

        top :: LaTeXC l => FracBinop -> l
        top FDiv = "/"

    tpprPrec p (FloatBinopE Pow e1 e2) =
        autoParensIf (p > powPrec) $
        tpprPrec appPrec1 e1 ^: tpprPrec powPrec e2

    tpprPrec _ (FloatBinopE Root e1 e2)
        | e1 == 2   = tsqrt Nothing (tppr e2)
        | otherwise = tsqrt (Just (tppr e1)) (tppr e2)

    tpprPrec p (FloatBinopE LogBase e1 e2) =
        autoParensIf (p > appPrec) $
        comm1 "mathop" (commS "log" !: tppr e1) <> braces (tpprPrec appPrec1 e2)

    tpprPrec p (DiffE e x) =
        autoParensIf (p > addPrec) $
        frac "d" ("d" <> tppr x) <> tpprPrec addPrec1 e

    tpprPrec _ (IntE Nothing e x) =
        integral <> tpprPrec addPrec1 e <> commS "," <> ("d" <> tppr x)

    tpprPrec _ (IntE (Just (l, u)) e x) =
        integralFromTo (tppr l) (tppr u) <> tpprPrec addPrec1 e <> commS "," <> ("d" <> tppr x)
