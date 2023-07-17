{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :  Hasksyma.Exp
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

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

  isConstE
) where

import Data.Symbol ( unintern, Symbol )
import IHaskell.Display ( IHaskellDisplay(..) )
import Text.LaTeX
    ( IsString(..), (!:), (^:), autoBrackets, operatorname, tsqrt )
import Text.LaTeX.Base.Class ( braces, comm1, commS, LaTeXC )
import Text.LaTeX.Base.Math ( frac )
import Text.PrettyPrint.Mainland ( Doc, (<+>), (<+/>), char, parensIf, text)
import Text.PrettyPrint.Mainland.Class ( Pretty(pprPrec, ppr) )

import Hasksyma.Const ( IsConst, Const )
import Hasksyma.LaTeX
    ( PrettyTeX(tpprPrec, tppr),
      autoParensIf,
      mathrel,
      tinfixop,
      displayMath )
import Hasksyma.Pretty
    ( HasFixity(..),
      Fixity,
      infixl_,
      infixr_,
      infixop,
      negPrec,
      negPrec1,
      mulPrec,
      mulPrec1,
      powPrec,
      powPrec1,
      appPrec,
      appPrec1 )

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

data Exp a where
    Undefined   :: Exp a
    Infty       :: Exp a
    NegInfty    :: Exp a
    ConstE      :: Const a -> Exp a
    VarE        :: Var -> Exp a
    NumUnopE    :: Num a => NumUnop -> Exp a -> Exp a
    FracUnopE   :: Fractional a => FracUnop -> Exp a -> Exp a
    FloatUnopE  :: (Floating a, Floating (Const a)) => FloatUnop -> Exp a -> Exp a
    NumBinopE   :: Num a => NumBinop -> Exp a -> Exp a -> Exp a
    IntPowE     :: Num a => Exp a -> Integer -> Exp a
    FracPowE    :: Fractional a => Exp a -> Integer -> Exp a
    IntBinopE   :: Integral a => IntBinop -> Exp a -> Exp a -> Exp a
    FracBinopE  :: Fractional a => FracBinop -> Exp a -> Exp a -> Exp a
    FloatBinopE :: (Floating a, Floating (Const a)) => FloatBinop -> Exp a -> Exp a -> Exp a

-- | Return 'True' if expression is a constant
isConstE :: Exp a -> Bool
isConstE ConstE{} = True
isConstE _        = False

deriving instance Show a => Show (Exp a)
deriving instance (Eq a, IsConst a) => Eq (Exp a)
deriving instance (Ord a, IsConst a) => Ord (Exp a)

instance (Num a, IsConst a, Eq (Exp a)) => Num (Exp a) where
    e1 + e2 = NumBinopE Add e1 e2
    e1 - e2 = NumBinopE Sub e1 e2
    e1 * e2 = NumBinopE Mul e1 e2

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

instance (Fractional a, IsConst a, Eq (Exp a)) => Fractional (Exp a) where
    (/) = FracBinopE FDiv

    recip = FracUnopE Recip

    fromRational = ConstE . fromRational

instance (Floating a, IsConst a, Floating (Const a), Eq (Exp a)) => Floating (Exp a) where
    pi = ConstE pi

    exp = FloatUnopE Exp

    log = FloatUnopE Log

    sqrt = FloatUnopE Sqrt

    (**) = FloatBinopE Pow

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
    ppr Exp    = "exp"
    ppr Log    = "log"
    ppr Sqrt   = "sqrt"
    ppr Sin    = "sin"
    ppr Cos    = "cos"
    ppr Tan    = "tan"
    ppr Asin   = "asin"
    ppr Acos   = "acos"
    ppr Atan   = "atan"
    ppr Sinh   = "sinh"
    ppr Cosh   = "cosh"
    ppr Tanh   = "tanh"
    ppr Asinh  = "asinh"
    ppr Acosh  = "acosh"
    ppr Atanh  = "atanh"

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
    pprPrec p (IntPowE e n)         = parensIf (p > powPrec) $
                                      pprPrec powPrec1 e <+> text "^" <+/> pprPrec powPrec n
    pprPrec p (FracPowE e n)        = parensIf (p > powPrec) $
                                      pprPrec powPrec1 e <+> text "^^" <+/> pprPrec powPrec n
    pprPrec p (IntBinopE op e1 e2)  = infixop p op e1 e2
    pprPrec p (FracBinopE op e1 e2) = infixop p op e1 e2

    pprPrec p (FloatBinopE Root e1 e2) =
        infixop p Pow e2 (recip e1)

    pprPrec p (FloatBinopE LogBase e1 e2) =
        parensIf (p > appPrec) $
        text "logBase" <+> pprPrec appPrec1 e1 <+> pprPrec appPrec1 e2

    pprPrec p (FloatBinopE op e1 e2) =
        infixop p op e1 e2

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
        top Exp    = comm1 "exp"
        top Log    = comm1 "log"
        top Sqrt   = error "can't happen"
        top Sin    = comm1 "sin"
        top Cos    = comm1 "cos"
        top Tan    = comm1 "tan"
        top Asin   = comm1 "arcsin"
        top Acos   = comm1 "arccos"
        top Atan   = comm1 "arctan"
        top Sinh   = comm1 "sinh"
        top Cosh   = comm1 "cosh"
        top Tanh   = comm1 "tanh"
        top Asinh  = comm1 "sinh^{-1}"
        top Acosh  = comm1 "cosh^{-1}"
        top Atanh  = comm1 "tanh^{-1}"

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
        (commS "log" !: tppr e1) <> braces (tpprPrec appPrec1 e2)

instance PrettyTeX (Exp a) => IHaskellDisplay (Exp a) where
    display = displayMath
