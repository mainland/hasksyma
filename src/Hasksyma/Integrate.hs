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

module Hasksyma.Integrate where

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

    -- Accumulate a constant coefficient and symbolic factors.
    fac :: Exp a
        -> Const a
        -> (Const a, [(Exp a, Const a)])
        -> (Const a, [(Exp a, Const a)])
    fac (ConstE k) n (k', fs) = (k' * k**n, fs)

    fac (NumUnopE Neg e) n (k, fs) =
      fac e n (-k, fs)

    fac (NumBinopE Mul e1 e2) n fs =
      fac e2 n (fac e1 n fs)

    fac (FracBinopE FDiv e1 e2) n fs =
      fac e2 (-n) (fac e1 n fs)

    fac (IntPowE e m) n fs =
      fac e (n*fromInteger m) fs

    fac (FracPowE e m) n fs =
      fac e (n*fromInteger m) fs

    fac (FloatBinopE Pow e (ConstE m)) n fs =
      fac e (n*m) fs

    fac e n (k, fs) = (k, addFactor e n fs)

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

-- | Form a heuristic quotient of factor lists by subtracting exponents.
-- Remove factors whose resulting exponent is zero.
divideFactors :: forall a . (Eq a, Floating a, Floating (Const a), IsConst a)
              => [(Exp a, Const a)] -- ^ Numerator factors
              -> [(Exp a, Const a)] -- ^ Denominator factors
              -> [(Exp a, Const a)] -- ^ Quotient factors
divideFactors ns0 ds0 = [(e, n) | (e, n) <- go ns0 ds0, n /= 0]
  where
    go :: [(Exp a, Const a)]
       -> [(Exp a, Const a)]
       -> [(Exp a, Const a)]
    go [] _      = []
    go ns  []    = ns
    go ns (d:ds) = go (div1 ns d) ds

    div1 :: [(Exp a, Const a)]
         -> (Exp a, Const a)
         -> [(Exp a, Const a)]
    div1 []            (e', m)             = [(e', -m)]
    div1 ((e, n) : fs) (e', m) | e' == e   = (e, n-m) : fs
                               | otherwise = (e, n) : div1 fs (e', m)

-- | Collect variables occurring in expression operands and integral bounds.
-- The variable fields of 'DiffE' and 'IntE' do not bind or add variables in
-- this traversal.
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
fvs (IntPowE e _)            = fvs e
fvs (FracPowE e _)           = fvs e
fvs (IntBinopE _ e1 e2)      = fvs e1 <> fvs e2
fvs (FracBinopE _ e1 e2)     = fvs e1 <> fvs e2
fvs (FloatBinopE _ e1 e2)    = fvs e1 <> fvs e2
fvs (DiffE e _)              = fvs e
fvs (IntE Nothing e _)       = fvs e
fvs (IntE (Just (l, u)) e _) = fvs l <> fvs u <> fvs e

-- | Test whether a variable is absent from the occurrences collected by 'fvs'.
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
derivDivides :: forall a m . (Ord a, Floating a, Floating (Const a), IsConst a, MonadPlus m)
             => Exp a              -- ^ Candidate base @u@
             -> Const a            -- ^ Constant exponent @n@
             -> Var                -- ^ Variable of integration @x@
             -> [(Exp a, Const a)] -- ^ Factors of the integrand
             -> m (Exp a)          -- ^ A candidate when substitution succeeds
derivDivides u n x fs | freeOf x k =
    if n == -1
    then pure $ k * log u
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

-- | Look up a candidate antiderivative for a unary 'Floating' operation.
-- Operations not represented in the table fail through 'mzero'.
tableIntegrate :: forall a m . (Eq a, Floating a, Floating (Const a), IsConst a, MonadPlus m)
               => FloatUnop         -- ^ Operation to integrate
               -> m (Exp a -> Exp a) -- ^ Candidate as a function of its argument
tableIntegrate Log  = pure $ \x -> x * log x - x
tableIntegrate Exp  = pure $ \x -> exp x
tableIntegrate Sin  = pure $ \x -> -cos x
tableIntegrate Cos  = pure $ \x -> sin x
tableIntegrate Tan  = pure $ \x -> -log (cos x)
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
