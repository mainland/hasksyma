-- |
-- Module      :  Hasksyma.Pretty
-- Copyright   :  (c) 2016-2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Hasksyma.Pretty (
    Fixity(..),
    Assoc(..),
    HasFixity(..),

    infix_,
    infixl_,
    infixr_,

    precOf,

    infixop,

    negPrec,
    negPrec1,
    addPrec,
    addPrec1,
    mulPrec,
    mulPrec1,
    powPrec,
    powPrec1,
    appPrec,
    appPrec1
  ) where

import Text.PrettyPrint.Mainland ( (<+/>), (<+>), parensIf, Doc )
import Text.PrettyPrint.Mainland.Class ( Pretty(pprPrec, ppr) )

-- | Operator fixity.
data Fixity = Fixity Assoc Int
  deriving (Eq, Ord)

-- | Operator associativity.
data Assoc = LeftAssoc | RightAssoc | NonAssoc
  deriving (Eq, Ord, Enum)

-- | Fixity for a non-fix operator.
infix_ :: Int -> Fixity
infix_ = Fixity NonAssoc

-- | Fixity for a left-associative operator.
infixl_ :: Int -> Fixity
infixl_ = Fixity LeftAssoc

-- | Fixity for a right-associative operator.
infixr_ :: Int -> Fixity
infixr_ = Fixity RightAssoc

-- | A type that has a fixity.
class HasFixity a where
    fixity :: a -> Fixity

-- | Return the precedence of a value with a fixity.
precOf :: HasFixity a => a -> Int
precOf op = p
  where
    Fixity _ p = fixity op

-- | Pretty-print an infix operator.
infixop :: (Pretty a, Pretty b, Pretty op, HasFixity op)
        => Int -- ^ precedence of context
        -> op  -- ^ operator
        -> a   -- ^ left argument
        -> b   -- ^ right argument
        -> Doc
infixop prec op l r =
    parensIf (prec > opPrec) $
    pprPrec leftPrec l <+> ppr op <+/> pprPrec rightPrec r
  where
    leftPrec | opAssoc == RightAssoc = opPrec + 1
             | otherwise             = opPrec

    rightPrec | opAssoc == LeftAssoc = opPrec + 1
              | otherwise            = opPrec

    Fixity opAssoc opPrec = fixity op

-- | Precedence of negation
negPrec, negPrec1 :: Int
negPrec = addPrec
negPrec1 = negPrec + 1

-- | Precedence of addition and subtraction
addPrec, addPrec1 :: Int
addPrec  = 6
addPrec1 = addPrec + 1

-- | Precedence of multiplication and division
mulPrec, mulPrec1 :: Int
mulPrec  = 7
mulPrec1 = mulPrec + 1

-- | Precedence of exponentiation
powPrec, powPrec1 :: Int
powPrec  = 8
powPrec1 = powPrec + 1

-- | Precedence of prefix function application
appPrec, appPrec1 :: Int
appPrec  = 10
appPrec1 = appPrec + 1
