{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module      :  Spiral.Util.Pretty.LaTeX
-- Copyright   :  (c) 2017-2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Hasksyma.LaTeX
    ( PrettyTeX(..),

      autoParensIf,
      mskip,
      mathbin,
      mathrel,
      nicefrac,

      tinfixop,

      displayMath,
    ) where

import Data.Complex (Complex(..))
#if defined(CYCLOTOMIC)
import Data.Complex.Cyclotomic ( Cyclotomic(..) )
#endif /* defined(CYCLOTOMIC) */
import Data.List ( intersperse )
#if defined(CYCLOTOMIC)
import qualified Data.Map as Map
import Data.Number.RealCyclotomic ( RealCyclotomic(..) )
#endif /* defined(CYCLOTOMIC) */
import Data.Ratio ( Ratio, numerator, denominator )
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Text as T
import IHaskell.Display
    ( latex, Display, IHaskellDisplay(display) )
import Text.LaTeX
    ( IsString(fromString),
      LaTeX,
      (!:),
      (^:),
      autoBraces,
      autoParens,
      autoSquareBrackets,
      math,
      showFloat,
      Render(render) )
#if defined(CYCLOTOMIC)
import Text.LaTeX
    ( (!^),
      zeta )
#endif /* defined(CYCLOTOMIC) */
import Text.LaTeX.Base.Class ( comm1, LaTeXC )
import Text.LaTeX.Packages.AMSFonts ( mathfrak )
import Text.PrettyPrint.Mainland ( strictText )
import Text.PrettyPrint.Mainland.Class ( Pretty(ppr) )

import Hasksyma.Pretty ( Assoc(..), Fixity(..), addPrec )

class PrettyTeX a where
    {-# MINIMAL tpprPrec | tppr #-}
    tppr     :: a -> LaTeX
    tpprPrec :: Int -> a -> LaTeX

    tpprList     :: [a] -> LaTeX
    tpprPrecList :: Int -> [a] -> LaTeX

    tppr       = tpprPrec 0
    tpprPrec _ = tppr

    tpprPrecList _ = tpprList
    tpprList       = autoSquareBrackets . commasep . map tppr

autoParensIf :: Bool -> LaTeX -> LaTeX
autoParensIf False l = l
autoParensIf True l  = autoParens l

hsep :: Monoid a => a -> [a] -> a
hsep sep = mconcat . intersperse sep

commasep :: [LaTeX] -> LaTeX
commasep = hsep ","

mskip :: LaTeX -> LaTeX
mskip = comm1 "mskip"

mathbin :: LaTeXC l => l -> l
mathbin = comm1 "mathbin"

mathrel :: LaTeXC l => l -> l
mathrel = comm1 "mathrel"

nicefrac :: LaTeX -> LaTeX -> LaTeX
nicefrac e1 e2 = mempty ^: e1 <> (mskip "-2mu" <> "/" <> mskip "-1mu") !: e2

instance PrettyTeX a => PrettyTeX [a] where
    tppr     = tpprList
    tpprPrec = tpprPrecList

instance PrettyTeX a => PrettyTeX (Set a) where
    tppr = autoBraces . commasep . map tppr . Set.toList

instance PrettyTeX Bool where
    tppr True  = mathfrak "T"
    tppr False = mathfrak "F"

tpprSignedIntegral :: (Integral a, Show a) => a -> LaTeX
tpprSignedIntegral x
    | x < 0     = "-" <> tpprSignedIntegral (-x)
    | otherwise = (fromString . show) x

tpprRealFloat :: (RealFloat a, Show a) => a -> LaTeX
tpprRealFloat x
    | isIntegral x = tppr (ceiling x :: Integer)
    | x < 0        = fromString $ showFloat (-x)
    | otherwise    = fromString $ showFloat x

isIntegral :: RealFrac a => a -> Bool
isIntegral x = fromIntegral (ceiling x :: Integer) == x

instance PrettyTeX Int where
    tppr = tpprSignedIntegral

instance PrettyTeX Integer where
    tppr = tpprSignedIntegral

instance PrettyTeX Float where
    tppr = tpprRealFloat

instance PrettyTeX Double where
    tppr = tpprRealFloat

instance (Eq a, Num a, PrettyTeX a) => PrettyTeX (Ratio a) where
    tppr x
      | d == 1    = tppr n
      | otherwise = nicefrac (tppr n) (tppr d)
      where
        n = numerator x
        d = denominator x

-- | Pretty-print an imaginary number
tpprIm :: (Eq a, Num a, PrettyTeX a) => a -> LaTeX
tpprIm 0    = mempty
tpprIm 1    = "i"
tpprIm (-1) = "-i"
tpprIm i    = tppr i <> "i"

instance (Eq a, Num a, PrettyTeX a) => PrettyTeX (Complex a) where
    tpprPrec _ (r :+ 0)    = tppr r
    tpprPrec _ (0 :+ 1)    = "i"
    tpprPrec _ (0 :+ (-1)) = "-i"
    tpprPrec _ (0 :+ i)    = tpprIm i
    tpprPrec p (r :+ i)    = autoParensIf (p > addPrec) $
                             case (T.unpack . render) (tpprIm i) of
                               '-' : _ -> tppr r <> tpprIm i
                               _       -> tppr r + tpprIm i

#if defined(CYCLOTOMIC)
instance PrettyTeX Cyclotomic where
    tpprPrec p (Cyclotomic n0 mp) =
        case Map.toList mp of
            []          -> "0"
            [(ex,rat)]  -> leadingTerm rat n0 ex
            (ex,rat):xs -> autoParensIf (p > addPrec) $
                           leadingTerm rat n0 ex <> mconcat (map (followingTerm n0) xs)
      where
        pprBaseExp :: Integer -> Integer -> LaTeX
        pprBaseExp n 1  = zeta !: tppr n
        pprBaseExp n ex = zeta !^ (tppr n, tppr ex)

        leadingTerm :: Rational -> Integer -> Integer -> LaTeX
        leadingTerm r _ 0 = tppr r
        leadingTerm r n ex
            | r == 1     = t
            | r == (-1)  = "-" <> t
            | r > 0      = tppr r <> t
            | r < 0      = "-" <> tppr (-r) <> t
            | otherwise  = mempty
            where
            t = pprBaseExp n ex

        followingTerm :: Integer -> (Integer, Rational) -> LaTeX
        followingTerm n (ex, r)
            | r == 1     = "+" <> t
            | r == (-1)  = "-" <> t
            | r > 0      = "+" <> tppr r <> t
            | r < 0      = "-" <> tppr (-r) <> t
            | otherwise  = mempty
            where
            t = pprBaseExp n ex

instance PrettyTeX RealCyclotomic where
    tpprPrec p (RealCyclotomic cyc) = tpprPrec p cyc
#endif /* defined(CYCLOTOMIC) */

-- | Pretty-print an infix operator.
tinfixop :: (PrettyTeX a, PrettyTeX b)
         => Int    -- ^ precedence of context
         -> Fixity -- ^ Fixity of operator
         -> LaTeX  -- ^ operator
         -> a      -- ^ left argument
         -> b      -- ^ right argument
         -> LaTeX
tinfixop prec (Fixity opAssoc opPrec) op l r =
    autoParensIf (prec > opPrec) $
    tpprPrec leftPrec l <> " " <> op <> " " <> tpprPrec rightPrec r
  where
    leftPrec | opAssoc == RightAssoc = opPrec + 1
             | otherwise             = opPrec

    rightPrec | opAssoc == LeftAssoc = opPrec + 1
              | otherwise            = opPrec

displayMath :: PrettyTeX a => a -> IO Display
displayMath = display . IHaskell.Display.latex . T.unpack . render . math . tppr

instance Pretty LaTeX where
    ppr = strictText . render . math
