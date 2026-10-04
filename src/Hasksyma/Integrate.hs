{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  Hasksyma.Integrate
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu
--
-- Heuristic symbolic integration and its factorization utilities.

module Hasksyma.Integrate
  ( Factors (..),
    factorize,
    unfactorize,
    fvs,
    freeOf,
    heuristicIntegrate,
    intFactors,
    derivDivides,
    divideFactors,
    tableIntegrate,
    deriv,
  )
where

import           Control.Monad
import           Data.List         (partition)
import           Data.Map          (Map)
import           Data.Set          (Set)
import qualified Data.Set          as Set

import           Hasksyma.Const
import           Hasksyma.Exp
import           Hasksyma.Simplify

-- | A constant coefficient and a map from symbolic bases to constant exponents.
data Factors a = F
    (Const a)              -- ^ Constant coefficient
    (Map (Exp a) (Const a)) -- ^ Bases and their exponents

-- | Decompose an expression into bases paired with constant exponents for the
-- integration heuristics. This uses algebraic product and power rewrites and
-- does not track their domain or branch conditions.
--
-- Decompose products, quotients, and powers with natural or signed integer
-- exponents. General powers are decomposed only when their exponent is an
-- 'IntegerC'. Keep 'FracPowE' and other general powers intact as bases with
-- integer multiplicities, avoiding distribution or merging of fractional
-- exponents across potentially negative or complex bases.
--
-- This changes the factor list for fractional powers: @x ** (1/2)@ is retained
-- as a whole factor with exponent one, rather than exposing @x@ with exponent
-- @1/2@. 'derivDivides' recognizes these intact factors for substitution.
-- Heuristics that require combining distinct fractional powers still need
-- domain and branch assumptions before that combination is valid.
-- Integer factor cancellation still uses formal algebra and does not track
-- excluded points or guarantee preservation of floating-point exceptions.
--
-- Collect exact rational coefficients without approximation. Other exact
-- constants, including nonzero multiples of pi, Euler's number, and irrational
-- cyclotomic values, remain symbolic bases. Their integer powers are retained
-- in the factor exponents. Known-zero bases with negative exponents also stay
-- symbolic. Rational coefficients may use 'RationalC' rather than their
-- original constant constructor.
factorize :: forall a . (Eq a, Floating a, Floating (Const a), IsConst a)
          => Exp a               -- ^ Expression to factor
          -> [(Exp a, Const a)] -- ^ Bases and their exponents
factorize e0 | k0 == 0   = [(0, 1)]
             | k0 == 1   = factors
             | otherwise = (ConstE k0, 1) : factors
  where
    k0 :: Const a
    factors :: [(Exp a, Const a)]
    (k0, factors) = fac e0 1 (1, [])

    -- Only integer exponents may enter recursive decomposition. Fractional
    -- powers remain whole factors so their domains and branches are retained.
    fac :: Exp a
        -> Integer
        -> (Const a, [(Exp a, Const a)])
        -> (Const a, [(Exp a, Const a)])
    fac e@(ConstE c) n (k, fs)
      | c == 0 && n < 0 = (k, addFactor e (fromInteger n) fs)
      | isExact c = case toRationalMaybe c of
                      Just q  -> (k * fromRational (q ^^ n), fs)
                      Nothing -> (k, addFactor e (fromInteger n) fs)
      | otherwise = (k * c ^^ n, fs)

    fac (NumUnopE Neg e) n (k, fs) =
      fac e n ((if even n then 1 else -1) * k, fs)

    fac (NumBinopE Mul e1 e2) n fs =
      fac e2 n (fac e1 n fs)

    fac (FracBinopE FDiv e1 e2) n fs =
      fac e2 (-n) (fac e1 n fs)

    fac (NatPowE e m) n fs =
      fac e (n*toInteger m) fs

    fac (IntPowE e m) n fs =
      fac e (n*m) fs

    fac (FloatBinopE Pow e (ConstE (IntegerC m))) n fs =
      fac e (n*m) fs

    fac e n (k, fs) = (k, addFactor e (fromInteger n) fs)

    -- Add a base, combining exponents when an equal base is present.
    addFactor :: Exp a
              -> Const a
              -> [(Exp a, Const a)]
              -> [(Exp a, Const a)]
    addFactor e n []                         = [(e, n)]
    addFactor e n ((e', m) : fs) | e' == e   = (e, n+m) : fs
                                 | otherwise = (e', m) : addFactor e n fs

-- | Reconstruct a product from bases paired with constant exponents.
unfactorize :: forall a . (Eq a, Floating a, Floating (Const a), IsConst a)
            => [(Exp a, Const a)]
            -> Exp a
unfactorize factors = product [e**ConstE n | (e, n) <- factors]

-- | Collect the expression's syntactic free-variable dependencies.
-- A definite integral binds its variable in the integrand, but not in either
-- bound. An indefinite integral retains its integration variable, even when
-- its integrand is constant. Differentiation propagates the operand's
-- dependencies without binding or adding its differentiation variable.
--
-- This is conservative dependency analysis without algebraic simplification.
-- Inclusion in the result does not prove that the value depends on a variable.
fvs :: Exp a -> Set Var
fvs Undefined{}              = mempty
fvs Infty{}                  = mempty
fvs NegInfty{}               = mempty
fvs ConstE{}                 = mempty
fvs (VarE v)                 = Set.singleton v
fvs (NumUnopE _ e)           = fvs e
fvs (FracUnopE _ e)          = fvs e
fvs (FloatUnopE _ e)         = fvs e
fvs (NumBinopE _ e1 e2)      = fvs e1 <> fvs e2
fvs (NatPowE e _)            = fvs e
fvs (IntPowE e _)            = fvs e
fvs (FracPowE e _)           = fvs e
fvs (IntBinopE _ e1 e2)      = fvs e1 <> fvs e2
fvs (FracBinopE _ e1 e2)     = fvs e1 <> fvs e2
fvs (FloatBinopE _ e1 e2)    = fvs e1 <> fvs e2
fvs (DiffE e _)              = fvs e
fvs (IntE Nothing e v)       = Set.insert v (fvs e)
fvs (IntE (Just (l, u)) e v) = fvs l <> fvs u <> Set.delete v (fvs e)

-- | Return 'True' if the variable is absent from the dependencies reported by
-- 'fvs'. A 'False' result does not establish actual dependence.
freeOf :: Var -> Exp a -> Bool
freeOf v e = v `Set.notMember` fvs e

-- | Search for antiderivative candidates using algebraic heuristics.
--
-- The result uses 'MonadPlus' to represent alternatives and failure. For
-- example, lists collect candidates and 'Maybe' selects the first success.
-- Domain and branch conditions are not recorded or checked.
heuristicIntegrate :: forall a m . (Ord a, Floating a, Floating (Const a), IsConst a, MonadPlus m)
                   => Exp a     -- ^ Expression to integrate
                   -> Var       -- ^ Variable of integration
                   -> m (Exp a) -- ^ Candidate antiderivatives
heuristicIntegrate e0 x = int e0
  where
    int :: Exp a -> m (Exp a)
    int e | freeOf x e        = pure $ e * VarE x
    int (NumUnopE Neg e)      = negate <$> int e
    int (NumBinopE Add e1 e2) = NumBinopE Add <$> int e1 <*> int e2
    int (NumBinopE Sub e1 e2) = NumBinopE Sub <$> int e1 <*> int e2
    int e                     = (unfactorize cs *) <$> intFactors fs x
      where
        cs, fs :: [(Exp a, Const a)]
        (cs, fs) = partition (\(u, _) -> freeOf x u) (factorize e)

-- | Integrate a product represented as bases paired with constant exponents.
--
-- The result is produced in 'MonadPlus' so callers may choose the first
-- successful heuristic, collect alternatives, or observe failure.
intFactors :: forall a m . (Ord a, Floating a, Floating (Const a), IsConst a, MonadPlus m)
           => [(Exp a, Const a)] -- ^ Factors of the integrand
           -> Var                -- ^ Variable of integration
           -> m (Exp a)          -- ^ A candidate when a heuristic succeeds
intFactors [] x = pure $ VarE x
intFactors fs x = msum [derivDivides u n x fs | (u, n) <- fs]

-- | Attempt integration by substitution. For a candidate factor @u^n@,
-- divide the integrand's factors by those of @u^n * du/dx@. A quotient
-- independent of @x@ supplies the multiplier for the candidate antiderivative.
--
-- An intact rational or constant general power with multiplicity one is also
-- a substitution candidate. Match that original factor when finding the
-- multiplier, without distributing its exponent or combining nested powers.
-- The power rule applies locally where the powers and derivatives are defined
-- on a consistent branch. This heuristic does not return domain conditions.
--
-- For exponent minus one, return @k * log (u^2) / 2@. This equals
-- @k * log (abs u)@ for nonzero real @u@, without introducing a complex
-- absolute value. It is a local complex antiderivative where @u^2@ avoids
-- zero and the chosen logarithm's branch cut.
derivDivides :: forall a m . (Ord a, Floating a, Floating (Const a), IsConst a, MonadPlus m)
             => Exp a              -- ^ Candidate base @u@
             -> Const a            -- ^ Constant exponent @n@
             -> Var                -- ^ Variable of integration @x@
             -> [(Exp a, Const a)] -- ^ Factors of the integrand
             -> m (Exp a)          -- ^ A candidate when substitution succeeds
derivDivides f n x fs
  | n == 1
  , Just (u, q) <- constantPower f
  , let k = unfactorize $ divideFactors fs ((f, 1) : factorize (deriv u x))
  , freeOf x k =
      if q == -1
      then pure $ k * log (NatPowE u 2) / 2
      else pure $ k * u ** ConstE (q+1) / ConstE (q+1)
  where
    -- Preserve the original factor for cancellation. Reconstructing it from
    -- its base and exponent can change constructors under partial evaluation.
    constantPower :: Exp a -> Maybe (Exp a, Const a)
    constantPower (FracPowE u q)                 = Just (u, fromRational q)
    constantPower (FloatBinopE Pow u (ConstE q)) = Just (u, q)
    constantPower _                              = Nothing

derivDivides u n x fs | freeOf x k =
    if n == -1
    then pure $ k * log (NatPowE u 2) / 2
    else pure $ k * u ** ConstE (n+1) / ConstE (n+1)
  where
    k :: Exp a
    k = unfactorize $ divideFactors fs $ factorize (u**ConstE n * deriv u x)

derivDivides f@(FloatUnopE op u) n x fs | n == 1 && freeOf x k = do
    g <- tableIntegrate op
    pure $ g u * k
  where
    k :: Exp a
    k = unfactorize $ divideFactors fs $ factorize (f * deriv u x)

derivDivides _ _ _ _ = mzero

-- | Form a heuristic quotient of factor lists by subtracting exponents.
-- Factors found only in the denominator are inserted with negated exponents.
-- Remove factors whose resulting exponent is zero. An empty factorization
-- represents one, so an empty numerator still requires processing every
-- denominator factor.
divideFactors :: forall a . (Eq a, Floating a, Floating (Const a), IsConst a)
              => [(Exp a, Const a)] -- ^ Numerator factors
              -> [(Exp a, Const a)] -- ^ Denominator factors
              -> [(Exp a, Const a)] -- ^ Quotient factors
divideFactors ns0 ds0 = [(e, n) | (e, n) <- go ns0 ds0, n /= 0]
  where
    go :: [(Exp a, Const a)]
       -> [(Exp a, Const a)]
       -> [(Exp a, Const a)]
    go ns  []    = ns
    go ns (d:ds) = go (div1 ns d) ds

    div1 :: [(Exp a, Const a)]
         -> (Exp a, Const a)
         -> [(Exp a, Const a)]
    div1 []            (e', m)             = [(e', -m)]
    div1 ((e, n) : fs) (e', m) | e' == e   = (e, n-m) : fs
                               | otherwise = (e, n) : div1 fs (e', m)

-- | Look up a candidate antiderivative for a unary 'Floating' operation.
-- Operations not represented in the table fail through 'mzero'.
-- Entries are local antiderivatives on domains where their operations and
-- derivatives are defined. The table does not return domain conditions.
--
-- 'Tan' uses @-log (cos x ^ 2) / 2@. For real arguments this equals
-- @-log (abs (cos x))@ wherever cosine is nonzero, covering intervals with
-- either sign of cosine. For complex arguments it is a local antiderivative
-- where the squared cosine avoids zero and the chosen logarithm's branch cut.
-- No complex absolute value is introduced, as that would lose analyticity.
tableIntegrate :: forall a m . (Eq a, Floating a, Floating (Const a), IsConst a, MonadPlus m)
               => FloatUnop         -- ^ Operation to integrate
               -> m (Exp a -> Exp a) -- ^ Candidate as a function of its argument
tableIntegrate Log  = pure $ \x -> x * log x - x
tableIntegrate Exp  = pure $ \x -> exp x
tableIntegrate Sin  = pure $ \x -> -cos x
tableIntegrate Cos  = pure $ \x -> sin x
tableIntegrate Tan  = pure $ \x -> -log (NatPowE (cos x) 2) / 2
tableIntegrate Sinh = pure $ \x -> cosh x
tableIntegrate Cosh = pure $ \x -> sinh x
tableIntegrate Tanh = pure $ \x -> log (cosh x)
tableIntegrate _    = mzero

-- | Compute (simplified) derivative of an expression
deriv :: (Ord a, Floating a, Floating (Const a), IsConst a)
      => Exp a
      -> Var
      -> Exp a
deriv e x = simplify (DiffE e x)
