{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}

-- |
-- Module      :  Hasksyma.Simplify
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu
--
-- Recursive simplification and single-step rewrite rules for expressions.

module Hasksyma.Simplify
  ( simplify,
    simplify',
    simplifyn,
    simplifyWithLimit,
    RewriteResult (..),
    rewriteWithLimit,
    mapExp,
    fixExp,
    simp,
  ) where

import           Data.Ratio      (denominator)
import           Numeric.Natural (Natural)

import           Hasksyma.Const  (Const (..), IsConst, isExact)
import           Hasksyma.Exp    (Exp (..), FloatBinop (..), FloatUnop (..), FracBinop (..),
                                  FracUnop (..), NumBinop (..), NumUnop (..), liftFloating,
                                  liftFloating2, liftFracPow, liftFractional, liftFractional2,
                                  liftIntPow, liftIntegral2, liftNatPow, liftNum, liftNum2, sameExp)

-- | Fully simplify an expression.
-- Iterate full bottom-up passes until 'sameExp' detects unchanged syntax.
-- There is no rewrite budget. Use 'simplifyWithLimit' to detect cycles or
-- stop after a bounded number of passes.
--
-- Logarithm sums and differences are not combined into logarithms of products
-- or quotients. Such transformations require domain and branch conditions
-- that this interface does not carry. Exponential/logarithm cancellation uses
-- explicit positive integer, rational, or named constants. Taking a logarithm
-- of a power additionally requires a rational exponent, and 'logBase' requires
-- a positive base other than one. Unknown conditions leave the operations
-- intact. Other algebraic rules still have domain restrictions, so this is
-- not a general guarantee of domain preservation.
--
-- Combining general floating powers, or flattening an integer power of one,
-- requires an explicitly positive exact base. Otherwise, retain the general
-- power to preserve possible domain failures at negative real bases.
--
-- Division by a known zero remains unreduced, as in @evalexact@.
-- No infinity or exceptional-value node is inferred from this operation.
-- Cancel structurally identical operands in @u/u@ and matching factors in
-- @(u*v)/u@ and @u*(v/u)@, including reversed factor orders. Reduce @0/u@
-- to zero unless @u@ is a known zero. These rules may extend the source domain,
-- including for nonfinite payloads and exceptional operands. Construction and
-- @evalexact@ retain unknown quotients. Combining different powers in a quotient,
-- or eliminating a negative exponent when combining powers, still requires an
-- explicit nonzero integer, rational, or named constant.
-- Cancelling nested reciprocals or flattening two negative integer powers
-- also requires an explicitly nonzero exact base. Otherwise the inner
-- reciprocal remains present, even if the combined exponent is positive.
--
-- Derivative rules give local formulas where the source expression and its
-- required derivatives are defined. They reduce child derivatives before
-- assembling product terms and omit terms with a known zero derivative.
-- Simplification can extend the derivative formula's domain, including when
-- its source contains a zero product. No derivative domain is returned or
-- certified.
--
-- Differentiating @log (abs u)@ retains the unresolved derivative of @abs u@.
-- The shortcut @u'/u@ requires nonzero real arguments and is invalid for general
-- complex values. This interface does not carry that domain evidence.
--
-- Negation folds constants only when its result has an exact representation,
-- as in @evalexact@. In particular, negated Euler's number remains symbolic.
-- Negated evaluated payloads also remain expression nodes. Use @eval@ to
-- request numerical reduction.
--
-- >>> :set -XOverloadedStrings
-- >>> import Hasksyma.Exp (Exp (..), NumBinop (..))
-- >>> let x = VarE "x" :: Exp Rational
-- >>> simplify (NumBinopE Add x 0) == x
-- True
simplify :: (Eq a, Num a, IsConst a) => Exp a -> Exp a
simplify e | sameExp e' e = e
           | otherwise    = simplify e'
  where
    e' = mapExp simp e

-- | Simplify by reaching a local fixed point at each non-leaf node through
-- 'fixExp'. Like 'simplify', this has no cycle or rewrite limit.
simplify' :: (Eq a, Num a, IsConst a) => Exp a -> Exp a
simplify' = fixExp simp

-- | Perform at most @n@ full simplification passes. A nonpositive budget
-- returns the input without rewriting. Stop at a fixed point or detected cycle,
-- discarding the completion status. Use 'simplifyWithLimit' when the
-- distinction between completion and an unfinished result matters.
simplifyn :: (Eq a, Num a, IsConst a) => Int -> Exp a -> Exp a
simplifyn n e = case simplifyWithLimit n e of
                  FixedPoint result       -> result
                  CycleDetected result    -> result
                  StepLimitReached result -> result

-- | The outcome of bounded rewriting. A fixed point means the supplied step
-- leaves syntax unchanged according to 'sameExp', not that an expression has a
-- mathematically canonical form.
data RewriteResult a
    = FixedPoint (Exp a)       -- ^ The last step left syntax unchanged.
    | CycleDetected (Exp a)    -- ^ A nontrivial cycle returned to this expression.
    | StepLimitReached (Exp a) -- ^ The budget ran out before establishing completion.
    deriving (Show)

-- | Apply a whole-expression rewrite step at most @n@ times, checking syntax
-- with 'sameExp'. A nonpositive budget returns 'StepLimitReached' with the
-- unchanged input and does not call the step. Detect fixed points and cycles
-- after each step, including the last permitted step.
--
-- Retain visited expressions for cycle detection within this budget. Each
-- step and identity comparison must itself terminate on finite expressions.
-- This is a step limit, not a time or expression-size limit. Custom payload
-- identity may fail to recognize a cycle, but the step budget still applies.
rewriteWithLimit :: (Eq a, IsConst a)
                 => Int -> (Exp a -> Exp a) -> Exp a -> RewriteResult a
rewriteWithLimit limit step = go limit []
  where
    go n _ e | n <= 0 = StepLimitReached e
    go n seen e
      | sameExp next e          = FixedPoint next
      | any (sameExp next) seen = CycleDetected next
      | otherwise               = go (n-1) (e:seen) next
      where
        next = step e

-- | Simplify with at most @n@ full bottom-up passes, reporting whether
-- rewriting reached a fixed point, found a cycle, or exhausted its budget.
-- The step and memory limitations of 'rewriteWithLimit' apply.
simplifyWithLimit :: (Eq a, Num a, IsConst a) => Int -> Exp a -> RewriteResult a
simplifyWithLimit n = rewriteWithLimit n (mapExp simp)

-- | Transform an expression bottom-up, including variables, constants, and
-- exceptional-value leaves. Rebuild each node with recursively transformed
-- children, then apply the callback. Syntax introduced by the callback is not
-- traversed again during this pass.
--
-- Traverse integral bounds and integrands, but leave the variable fields of
-- 'DiffE' and 'IntE' unchanged. This is a syntactic transformation, not
-- capture-avoiding substitution. Callbacks must handle leaf constructors.
mapExp :: (Eq a, IsConst a) => (Exp a -> Exp a) -> Exp a -> Exp a
mapExp f e@Undefined{}            = f e
mapExp f e@Infty{}                = f e
mapExp f e@NegInfty{}             = f e
mapExp f e@ConstE{}               = f e
mapExp f e@VarE{}                 = f e
mapExp f (NumUnopE op x)          = f (NumUnopE op (mapExp f x))
mapExp f (FracUnopE op x)         = f (FracUnopE op (mapExp f x))
mapExp f (FloatUnopE op x)        = f (FloatUnopE op (mapExp f x))
mapExp f (NumBinopE op x y)       = f (NumBinopE op (mapExp f x) (mapExp f y))
mapExp f (NatPowE x n)            = f (NatPowE (mapExp f x) n)
mapExp f (IntPowE x n)            = f (IntPowE (mapExp f x) n)
mapExp f (FracPowE x q)           = f (FracPowE (mapExp f x) q)
mapExp f (IntBinopE op x y)       = f (IntBinopE op (mapExp f x) (mapExp f y))
mapExp f (FracBinopE op x y)      = f (FracBinopE op (mapExp f x) (mapExp f y))
mapExp f (FloatBinopE op x y)     = f (FloatBinopE op (mapExp f x) (mapExp f y))
mapExp f (DiffE x v)              = f (DiffE (mapExp f x) v)
mapExp f (IntE Nothing x v)       = f (IntE Nothing (mapExp f x) v)
mapExp f (IntE (Just (l, u)) x v) = f (IntE (Just (mapExp f l, mapExp f u)) (mapExp f x) v)

-- | Recursively apply a function to an expression and its sub-expressions until
-- reaching a local fixed point under 'sameExp'. Leaf nodes are returned
-- unchanged. This unbounded traversal can diverge for cycling rules. For
-- bounded whole-expression steps use 'rewriteWithLimit'.
fixExp :: (Eq a, IsConst a) => (Exp a -> Exp a) -> Exp a -> Exp a
fixExp _ e@Undefined{} = e
fixExp _ e@Infty{}     = e
fixExp _ e@NegInfty{}  = e
fixExp _ e@ConstE{}    = e
fixExp _ e@VarE{}      = e

fixExp f e
    | sameExp e' e = e
    | otherwise   = fixExp f e'
  where
    e' = step e

    step (NumUnopE op x)          = f (NumUnopE op (fixExp f x))
    step (FracUnopE op x)         = f (FracUnopE op (fixExp f x))
    step (FloatUnopE op x)        = f (FloatUnopE op (fixExp f x))
    step (NumBinopE op x y)       = f (NumBinopE op (fixExp f x) (fixExp f y))
    step (NatPowE x n)            = f (NatPowE (fixExp f x) n)
    step (IntPowE x n)            = f (IntPowE (fixExp f x) n)
    step (FracPowE x q)           = f (FracPowE (fixExp f x) q)
    step (IntBinopE op x y)       = f (IntBinopE op (fixExp f x) (fixExp f y))
    step (FracBinopE op x y)      = f (FracBinopE op (fixExp f x) (fixExp f y))
    step (FloatBinopE op x y)     = f (FloatBinopE op (fixExp f x) (fixExp f y))
    step (DiffE x v)              = f (DiffE (fixExp f x) v)
    step (IntE Nothing x v)       = f (IntE Nothing (fixExp f x) v)
    step (IntE (Just (l, u)) x v) = f (IntE (Just (fixExp f l, fixExp f u)) (fixExp f x) v)
    step leaf                     = leaf

-- | An expression consisting of exponentiation.
data Pow a where
    NatPow   :: Num a => Exp a -> Natural -> Pow a
    IntPow   :: Fractional a => Exp a -> Integer -> Pow a
    FracPow  :: (Floating a, Floating (Const a)) => Exp a -> Rational -> Pow a
    FloatPow :: (Floating a, Floating (Const a)) => Exp a -> Exp a -> Pow a

base :: Pow a -> Exp a
base (NatPow e _)   = e
base (IntPow e _)   = e
base (FracPow e _)  = e
base (FloatPow e _) = e

pow :: (Eq a, Num a, IsConst a) => Exp a -> Maybe (Pow a)
pow e@VarE{}               = Just (NatPow e 1)
pow (NatPowE e n)          = Just (NatPow e n)
pow (IntPowE e n)          = Just (IntPow e n)
pow (FracPowE e q)         = Just (FracPow e q)
pow (FracUnopE Recip e)    = Just (IntPow e (-1))
pow (FloatUnopE Exp n)     = Just (FloatPow (ConstE E) n)
pow (FloatUnopE Sqrt e)    = Just (FracPow e (1/2))
pow (FloatBinopE Pow e n)  = Just (FloatPow e n)
pow (FloatBinopE Root (ConstE (IntegerC n)) e)
    | n /= 0 = Just (FracPow e (1/fromInteger n))
pow (FloatBinopE Root (ConstE (RationalC q)) e)
    | q /= 0 = Just (FracPow e (1/q))
pow (FloatBinopE Root n e) = Just (FloatPow e (1/n))
pow _                      = Nothing

joinPowWith :: (Eq a, IsConst a)
            => (Pow a -> Pow a -> b)
            -> Pow a
            -> Pow a
            -> b
joinPowWith f x@NatPow{}   y@NatPow{}         = f x y
joinPowWith f x@IntPow{}   y@IntPow{}         = f x y
joinPowWith f x@FracPow{}  y@FracPow{}        = f x y
joinPowWith f x@FloatPow{} y@FloatPow{}       = f x y

joinPowWith f (NatPow e1 n)  (IntPow e2 m)    = f (IntPow e1 (toInteger n)) (IntPow e2 m)
joinPowWith f (IntPow e1 n)  (NatPow e2 m)    = f (IntPow e1 n) (IntPow e2 (toInteger m))
joinPowWith f (NatPow e1 n)  (FracPow e2 q)   = f (FracPow e1 (fromIntegral n)) (FracPow e2 q)
joinPowWith f (FracPow e1 q) (NatPow e2 n)    = f (FracPow e1 q) (FracPow e2 (fromIntegral n))
joinPowWith f (IntPow e1 n)  (FracPow e2 q)   = f (FracPow e1 (fromInteger n)) (FracPow e2 q)
joinPowWith f (FracPow e1 q) (IntPow e2 n)    = f (FracPow e1 q) (FracPow e2 (fromInteger n))

joinPowWith f (NatPow e1 n)   (FloatPow e2 m) = f (FloatPow e1 (fromIntegral n)) (FloatPow e2 m)
joinPowWith f (FloatPow e1 n) (NatPow e2 m)   = f (FloatPow e1 n) (FloatPow e2 (fromIntegral m))
joinPowWith f (IntPow e1 n)   (FloatPow e2 m) = f (FloatPow e1 (fromInteger n)) (FloatPow e2 m)
joinPowWith f (FloatPow e1 n) (IntPow e2 m)   = f (FloatPow e1 n) (FloatPow e2 (fromInteger m))
joinPowWith f (FracPow e1 q)  (FloatPow e2 m) = f (FloatPow e1 (fromRational q)) (FloatPow e2 m)
joinPowWith f (FloatPow e1 n) (FracPow e2 q)  = f (FloatPow e1 n) (FloatPow e2 (fromRational q))

-- General floating exponents can become integral after combining, erasing a
-- domain failure at a negative real base. A positive exact base justifies the
-- exponent law. Fractional powers with unknown bases retain the more limited
-- check against combining into an integral exponent. Combining a negative
-- exponent into a nonnegative one additionally requires a known nonzero base.
canCombinePowers :: (Rational -> Rational -> Rational) -> Pow a -> Pow a -> Bool
-- For example, x^(-1) * x would become one and lose x /= 0.
-- This guard is intentionally stricter than ordinary factor cancellation.
canCombinePowers f p1 p2
    | Just q <- rationalPower p1, Just r <- rationalPower p2
    , q < 0 || r < 0, f q r >= 0
    , not (isNonzeroExactConstant (base p1)) = False
canCombinePowers _ (FloatPow x _) _ = isPositiveExactConstant x
canCombinePowers _ _ (FloatPow x _) = isPositiveExactConstant x
canCombinePowers f (FracPow _ q) p =
    maybe False (\r -> denominator (f q r) /= 1) (rationalPower p)
canCombinePowers f p (FracPow _ r) =
    maybe False (\q -> denominator (f q r) /= 1) (rationalPower p)
canCombinePowers _ _ _ = True

rationalPower :: Pow a -> Maybe Rational
rationalPower (NatPow _ n)  = Just (fromIntegral n)
rationalPower (IntPow _ n)  = Just (fromInteger n)
rationalPower (FracPow _ q) = Just q
rationalPower FloatPow{}    = Nothing

sumbefore :: (Eq a, Num a, IsConst a) => Exp a -> Exp a -> Bool
sumbefore ConstE{}           ConstE{}           = False
sumbefore _                  ConstE{}           = True
sumbefore (VarE x)           (VarE y)           = x < y
sumbefore (NumUnopE op1 _)   (NumUnopE op2 _)   = op1 < op2
sumbefore (FracUnopE op1 _)  (FracUnopE op2 _)  = op1 < op2
sumbefore (FloatUnopE op1 _) (FloatUnopE op2 _) = op1 < op2

sumbefore (NumBinopE Mul ConstE{} x) (NumBinopE Mul ConstE{} y) = x `sumbefore` y
sumbefore (NumBinopE Mul ConstE{} x) y                          = x `sumbefore` y
sumbefore x                          (NumBinopE Mul ConstE{} y) = x `sumbefore` y

-- Note that we /reverse/ the comparison for expressions in the denominator
sumbefore (FracBinopE FDiv _ x) (FracBinopE FDiv _ y) = y `sumbefore` x

sumbefore (pow -> Just p1) (pow -> Just p2)
    | base p1 == base p2 = joinPowWith go p1 p2
    | otherwise          = base p1 `sumbefore` base p2
  where
    go (NatPow _ n)   (NatPow _ m)   = n < m
    go (IntPow _ n)   (IntPow _ m)   = n < m
    go (FracPow _ q)  (FracPow _ r)  = q < r
    go (FloatPow _ n) (FloatPow _ m) = sumbefore n m
    go _              _              = False

sumbefore _ _ = False

prodbefore :: (Eq a, Num a, IsConst a) => Exp a -> Exp a -> Bool
prodbefore ConstE{}           ConstE{}           = False
prodbefore ConstE{}           _                  = True
prodbefore (VarE x)           (VarE y)           = x < y
prodbefore x                  (NumUnopE Neg y)   = x `prodbefore` y

prodbefore (pow -> Just p1) (pow -> Just p2)
    | base p1 == base p2 = joinPowWith go p1 p2
    | otherwise          = base p1 `prodbefore` base p2
  where
    go (NatPow _ n)   (NatPow _ m)   = n < m
    go (IntPow _ n)   (IntPow _ m)   = n < m
    go (FracPow _ q)  (FracPow _ r)  = q < r
    go (FloatPow _ n) (FloatPow _ m) = prodbefore n m
    go _              _              = False

prodbefore NatPowE{}          FloatUnopE{}       = True
prodbefore IntPowE{}          FloatUnopE{}       = True
prodbefore FracPowE{}         FloatUnopE{}       = True
prodbefore (NatPowE x _)      y                  = x `prodbefore` y
prodbefore (IntPowE x _)      y                  = x `prodbefore` y
prodbefore (FracPowE x _)     y                  = x `prodbefore` y
prodbefore (NumUnopE op1 _)   (NumUnopE op2 _)   = op1 < op2
prodbefore (FracUnopE op1 _)  (FracUnopE op2 _)  = op1 < op2
prodbefore (FloatUnopE op1 _) (FloatUnopE op2 _) = op1 < op2

prodbefore _ _ = False

-- Conservatively recognize positivity from exact syntax, without evaluating
-- payloads or assuming that variables are real.
isPositiveExactConstant :: Exp a -> Bool
isPositiveExactConstant (ConstE (IntegerC n))  = n > 0
isPositiveExactConstant (ConstE (RationalC q)) = q > 0
isPositiveExactConstant (ConstE (Pi q))        = q > 0
isPositiveExactConstant (ConstE E)             = True
isPositiveExactConstant _                      = False

-- Nonzero evidence must come from exact syntax, not inequality with zero:
-- opaque payloads can contain infinities or NaNs, and variables can be zero.
isNonzeroExactConstant :: Exp a -> Bool
isNonzeroExactConstant (ConstE (IntegerC n))  = n /= 0
isNonzeroExactConstant (ConstE (RationalC q)) = q /= 0
isNonzeroExactConstant (ConstE (Pi q))        = q /= 0
isNonzeroExactConstant (ConstE E)             = True
isNonzeroExactConstant _                      = False

-- | One-step expression simplification. Derivative rules reduce child
-- derivatives when assembling product terms, as described in 'simplify'.
simp :: forall a . (Eq a, Num a, IsConst a) => Exp a -> Exp a
-- Keep nested inverses unless the base is known nonzero: cancelling
-- recip (recip 0) would erase the inner singularity. This is a
-- conservative policy, unlike the domain-extending factor rules below.
simp (FracUnopE Recip (FracUnopE Recip x)) | isNonzeroExactConstant x = x

simp (NumBinopE Add x y)
  | x == 0  = y
  | y == 0  = x
  | x == y  = 2 * x
  | y == -x = 0

simp (NumBinopE Sub x y)
  | x == 0 = -y
  | y == 0 = x
  | x == y = 0

simp (NumBinopE Mul x y)
  | x == 0    = 0
  | y == 0    = 0
  | x == 1    = y
  | y == 1    = x
  | x == y    = NatPowE x 2

-- Leave known-zero division to numerical evaluation. A blanket infinity
-- would give the wrong sign for (-1)/0 and the wrong behavior for 0/0
-- or exact rational division.
simp e@(FracBinopE FDiv x y)
  | y == 0      = e
  | x == 0      = 0
  | x == 1      = IntPowE y (-1)
  | y == 1      = x
  | sameExp x y = 1

-- Cancel matching factors before rearranging products and quotients.
simp (NumBinopE Mul x (FracBinopE FDiv y x')) | sameExp x' x =
    y

simp (NumBinopE Mul (FracBinopE FDiv y x) x') | sameExp x' x =
    y

simp (FracBinopE FDiv (NumBinopE Mul x y) x') | sameExp x' x =
    y

simp (FracBinopE FDiv (NumBinopE Mul y x) x') | sameExp x' x =
    y

-- Add constants: x + k1 + k2 = x + (k1 + k2)
--
-- We need this rewrite since constants are moved to the end of a sum.
--
-- We /do not/ need the analogous rewrite for multiplication since constants are
-- moved to the /beginning/ of a product where the will be caught by the final
-- rules using @'liftNum2'@.
simp (NumBinopE Add (NumBinopE Add x (ConstE n)) (ConstE m)) | isExact y =
    x + ConstE y
  where
    y = n + m

-- Re-associate terms in sum: x + (y + z) => x + y + z
simp (NumBinopE Add x (NumBinopE Add y z)) =
    x + y + z

-- Reorder terms in sum
simp (NumBinopE Add x y) | y `sumbefore` x =
    y + x

simp (NumBinopE Sub x y) | y `sumbefore` x =
    -y + x

simp (NumBinopE Add (NumBinopE Add x y) z) | z `sumbefore` y =
    x + z + y

-- Re-associate terms in product: x * (y * z) => x * y * z
simp (NumBinopE Mul x (NumBinopE Mul y z)) =
    x * y * z

-- Reorder terms in product
simp (NumBinopE Mul x y) | y `prodbefore` x =
    y * x

simp (NumBinopE Mul (NumBinopE Mul x y) z) | z `prodbefore` y =
    x * z * y

simp (FracBinopE FDiv (NumBinopE Mul x y) z) | z `prodbefore` y =
    x/z * y

simp (NumBinopE Mul x (FracBinopE FDiv y z)) | z `prodbefore` y =
    x/z * y

-- Simplify negation
-- Do not fold arbitrary constants here: negating symbolic E would
-- approximate it. Leave constant negation to the exactness-checked
-- liftNum fall-through rule.
simp (NumUnopE Neg (NumUnopE Neg x)) = x

simp (NumBinopE Add x (NumUnopE Neg y)) =
    x - y

simp (NumBinopE Sub x (NumUnopE Neg y)) =
    x + y

simp (NumBinopE Mul (NumUnopE Neg x) y) =
    -(x*y)

simp (NumBinopE Mul x (NumUnopE Neg y)) =
    -(x*y)

simp (FracBinopE FDiv (NumUnopE Neg x) y) =
    -(x/y)

simp (FracBinopE FDiv x (NumUnopE Neg y)) =
    -(x/y)

-- Distribute multiplication/division over addition/subtraction
simp (NumBinopE Mul x (NumBinopE Add y z)) =
    x*y + x*z

simp (NumBinopE Mul x (NumBinopE Sub y z)) =
    x*y - x*z

simp (FracBinopE FDiv (NumBinopE Add y z) x) =
    y/x + z/x

simp (FracBinopE FDiv (NumBinopE Sub y z) x) =
    y/x - z/x

-- Simplify exponentiation
simp (NumBinopE Mul (IntPowE x n) y) | n < 0 =
    y / NatPowE x (fromInteger (-n))

simp (NumBinopE Mul (pow -> Just p1) (pow -> Just p2))
    | base p1 == base p2, canCombinePowers (+) p1 p2 =
    joinPowWith mulPowers p1 p2

simp (NumBinopE Mul (NumBinopE Mul e (pow -> Just p1)) (pow -> Just p2))
    | base p1 == base p2, canCombinePowers (+) p1 p2 =
    NumBinopE Mul e $ joinPowWith mulPowers p1 p2

-- Subtracting exponents can erase excluded zeros: x^3/x^2 becomes x.
-- Retain the nonzero-base guard as a conservative power-rule policy,
-- even though matching-factor cancellation above permits domain extension.
simp (FracBinopE FDiv (pow -> Just p1) (pow -> Just p2))
    | base p1 == base p2, isNonzeroExactConstant (base p1), canCombinePowers (-) p1 p2 =
    joinPowWith go p1 p2
  where
    go (NatPow x n)   (NatPow _ m)   = IntPowE x (toInteger n - toInteger m)
    go (IntPow x n)   (IntPow _ m)   = IntPowE x (n - m)
    go (FracPow x q)  (FracPow _ r)  = FracPowE x (q - r)
    go (FloatPow x n) (FloatPow _ m) = FloatBinopE Pow x (n - m)
    go _              _              = error "can't happen"

-- Keep fractional inner powers intact when an outer integral power could
-- erase real-domain failures, such as (sqrt (-1))^2 becoming -1.
-- This restriction is a conservative domain policy.
-- General floating inner powers likewise require a positive exact base.
simp (pow -> Just p) = go p
  where
    go :: Pow a -> Exp a
    -- Integral powers use the empty-product convention, including 0^0 = 1.
    go (NatPow x n)
      | n == 0 = 1
      | n == 1 = x

    go (NatPow e@(pow -> Just p1) n) =
        case p1 of
          NatPow x m   -> NatPowE x (n*m)
          IntPow x m   -> IntPowE x (toInteger n*m)
          FracPow{}    -> liftNatPow e n
          FloatPow x m
            | isPositiveExactConstant x -> FloatBinopE Pow x (fromIntegral n*m)
            | otherwise                 -> liftNatPow e n

    go (NatPow x n) =
        liftNatPow x n

    go (IntPow x n)
      | n == 0 = 1
      | n == 1 = x
      | n >= 0 = NatPowE x (fromInteger n)

    go (IntPow e@(pow -> Just p1) n) =
        case p1 of
          NatPow x m   -> IntPowE x (n*toInteger m)
          -- Only negative outer exponents reach this branch. Flattening a
          -- negative inner exponent would remove its nonzero requirement.
          IntPow x m
            | m >= 0 || isNonzeroExactConstant x -> IntPowE x (n*m)
            | otherwise                          -> liftIntPow e n
          FracPow{}    -> liftIntPow e n
          FloatPow x m
            | isPositiveExactConstant x -> FloatBinopE Pow x (fromInteger n*m)
            | otherwise                 -> liftIntPow e n

    go (IntPow x n) =
        liftIntPow x n

    go (FracPow x q) =
        liftFracPow x q

    -- This guard preserves real-domain failures at negative x. The identity
    -- exp(log x) = x holds for nonzero complex x, but the numerical carrier
    -- need not be complex. Positivity is a conservative sufficient condition.
    go (FloatPow (ConstE E) (FloatUnopE Log x)) | isPositiveExactConstant x =
        x

    go (FloatPow x (ConstE (IntegerC n))) =
        IntPowE x n

    go (FloatPow x (ConstE (RationalC q))) =
        liftFracPow x q

    go (FloatPow e1 e2) = liftFloating2 Pow e1 e2

-- Trigonometric simplification
simp (FloatUnopE Sin n) | n == 0 = 0

simp (FloatUnopE Sin (ConstE (Pi k)))
    | k == 1   = 0
    | k == 1/2 = 1

simp (FloatUnopE Cos n) | n == 0 = 1

simp (FloatUnopE Cos (ConstE (Pi k)))
    | k == 1   = -1
    | k == 1/2 = 0

simp (NumBinopE Add (NatPowE (FloatUnopE Sin x) 2) (NatPowE (FloatUnopE Cos x') 2)) | x' == x =
    1

-- Do not combine logarithm sums or differences without branch conditions.
-- For principal complex logs, log(-1) + log(-1) = 2*pi*i, not log(1),
-- and log(-i) - log(i) = -pi*i, not log(-1). Positive real arguments
-- justify both laws, but this interface carries no such assumptions.
-- The same restriction applies to logBase sums and differences.

-- Simplify logs
simp (FloatUnopE Log x)
    | x == 1 = 0

-- log(exp z) = z fails across the principal logarithm branch cut.
-- For z = 2*pi*i, the left side is zero. Cancel only the explicitly
-- real integral and rational exponents, not a general exponent.
simp e@(FloatUnopE Log (pow -> Just p)) | base p == ConstE E = go p
  where
    go (NatPow _ n)  = fromIntegral n
    go (IntPow _ n)  = fromInteger n
    go (FracPow _ q) = fromRational q
    go FloatPow{}    = e

simp (FloatBinopE LogBase (ConstE E) x) =
    log x

-- Use the real-base conditions b > 0 and b /= 1 for these inverse rules.
-- In particular, logBase 1 1 is an undefined quotient, not zero. General
-- exponents still need branch information, as for log(exp z) above.
simp (FloatBinopE LogBase b x)
    | isPositiveExactConstant b, b /= 1, x == 1 = 0

simp e@(FloatBinopE LogBase b (pow -> Just p))
    | isPositiveExactConstant b, b /= 1, base p == b = go p
  where
    go (NatPow _ n)  = fromIntegral n
    go (IntPow _ n)  = fromInteger n
    go (FracPow _ q) = fromRational q
    go FloatPow{}    = e

-- Simplify differentiation
simp (DiffE ConstE{} _) =
    0

simp (DiffE (VarE x) x')
    | x' == x   = 1
    | otherwise = 0

simp (DiffE (NumUnopE Neg u) x) =
    mapExp simp $ negate (DiffE u x)

simp (DiffE (NumBinopE Add u v) x) =
    mapExp simp $ DiffE u x + DiffE v x

simp (DiffE (NumBinopE Sub u v) x) =
    mapExp simp $ DiffE u x - DiffE v x

simp (DiffE (NumBinopE Mul u v) x) =
    simp $ NumBinopE Add (derivativeTerm u (DiffE v x)) (derivativeTerm v (DiffE u x))

simp (DiffE (FracBinopE FDiv u v) x) =
    (derivativeTerm v (DiffE u x) - derivativeTerm u (DiffE v x)) / v ^ (2 :: Integer)

simp (DiffE (NatPowE _ 0) _) = 0

-- The preceding zero case ensures the decremented exponent is nonnegative.
simp (DiffE (NatPowE u n) x) =
    derivativeTerm (fromIntegral n * NatPowE u (fromInteger (toInteger n-1))) (DiffE u x)

simp (DiffE (IntPowE _ 0) _) = 0

simp (DiffE (IntPowE u n) x) =
    derivativeTerm (fromIntegral n * u ^^ (n-1)) (DiffE u x)

simp (DiffE (FracPowE _ 0) _) = 0

simp (DiffE (FracPowE u q) x) =
    derivativeTerm (fromRational q * FracPowE u (q-1)) (DiffE u x)

simp (DiffE (FloatBinopE Pow _ (ConstE (IntegerC 0))) _) = 0

simp (DiffE (FloatBinopE Pow _ (ConstE (RationalC 0))) _) = 0

simp (DiffE (FloatBinopE Pow u v) x) =
    simp $ NumBinopE Add (derivativeTerm (v * u ** (v-1)) (DiffE u x))
                        (derivativeTerm (u ** v * log u) (DiffE v x))

simp (DiffE (FloatUnopE Exp u) x) =
    derivativeTerm (FloatUnopE Exp u) (DiffE u x)

-- Do not special-case log(abs u) as u'/u without real, nonzero u.
-- As a function of complex z, log(abs z) is not holomorphic. Retain
-- the derivative of abs u until a rule with real-domain evidence applies.
simp (DiffE (FloatUnopE Log u) x) =
    DiffE u x / u

simp (DiffE (FloatUnopE Sin u) x) =
    derivativeTerm (cos u) (DiffE u x)

simp (DiffE (FloatUnopE Cos u) x) =
    derivativeTerm (-(sin u)) (DiffE u x)

simp (DiffE (FloatUnopE Sinh u) x) =
    derivativeTerm (cosh u) (DiffE u x)

simp (DiffE (FloatUnopE Cosh u) x) =
    derivativeTerm (sinh u) (DiffE u x)

-- Fall-through rules. These will combine constants when possible.
simp (NumUnopE op x)      = liftNum op x
simp (FracUnopE op x)     = liftFractional op x
simp (FloatUnopE op x)    = liftFloating op x
simp (NumBinopE op x y)   = liftNum2 op x y
simp (NatPowE e n)        = liftNatPow e n
simp (IntPowE e n)        = liftIntPow e n
simp (FracPowE e q)       = liftFracPow e q
simp (IntBinopE op x y)   = liftIntegral2 op x y
simp (FloatBinopE op x y) = liftFloating2 op x y
simp (FracBinopE op x y)  = liftFractional2 op x y

simp e = e

-- Derivative formulas apply locally where the source and its required
-- derivatives are defined. Omit a term with a known zero derivative in this
-- context before constructing potentially branch-sensitive coefficients. The
-- child derivative is reduced before the coefficient is needed. Use a single
-- bottom-up pass, not an unbounded fixed-point loop inside a rewrite step.
derivativeTerm :: (Eq a, Num a, IsConst a) => Exp a -> Exp a -> Exp a
derivativeTerm coefficient derivative
    | d == 0   = 0
    | otherwise = coefficient * d
  where
    d = mapExp simp derivative

-- | Multiply exponents with equal bases
mulPowers :: (Eq a, IsConst a) => Pow a -> Pow a -> Exp a
mulPowers (NatPow x n)   (NatPow _ m)   = NatPowE x (n + m)
mulPowers (IntPow x n)   (IntPow _ m)   = IntPowE x (n + m)
mulPowers (FracPow x q)  (FracPow _ r)  = FracPowE x (q + r)
mulPowers (FloatPow x n) (FloatPow _ m) = FloatBinopE Pow x (n + m)
mulPowers _              _              = error "can't happen"
