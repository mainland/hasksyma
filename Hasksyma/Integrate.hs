{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      :  Hasksyma.Integrate
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Hasksyma.Integrate where

import Control.Monad
import Data.List ( partition )
import Data.Map ( Map )
import Data.Set ( Set )
import qualified Data.Set as Set

import Hasksyma.Const
import Hasksyma.Exp
import Hasksyma.Simplify

data Factors a = F (Const a) (Map (Exp a) (Const a))

factorize :: forall a . (Eq a, Floating a, Floating (Const a), IsConst a)
          => Exp a
          -> [(Exp a, Const a)]
factorize e0 | k0 == 0   = [(0, 1)]
             | k0 == 1   = factors
             | otherwise = (ConstE k0, 1) : factors
  where
    k0 :: Const a
    factors :: [(Exp a, Const a)]
    (k0, factors) = fac e0 1 (1, [])

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

    addFactor :: Exp a
              -> Const a
              -> [(Exp a, Const a)]
              -> [(Exp a, Const a)]
    addFactor e n []                         = [(e, n)]
    addFactor e n ((e', m) : fs) | e' == e   = (e, n+m) : fs
                                 | otherwise = (e', m) : addFactor e n fs

unfactorize :: forall a . (Eq a, Floating a, Floating (Const a), IsConst a)
            => [(Exp a, Const a)]
            -> Exp a
unfactorize factors = foldl (*) 1 [e**ConstE n | (e, n) <- factors]

divideFactors :: forall a . (Eq a, Floating a, Floating (Const a), IsConst a)
              => [(Exp a, Const a)]
              -> [(Exp a, Const a)]
              -> [(Exp a, Const a)]
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

freeOf :: Var -> Exp a -> Bool
freeOf v e = v `Set.notMember` fvs e

heuristicIntegrate :: forall a m . (Ord a, Floating a, Floating (Const a), IsConst a, MonadPlus m)
                   => Exp a
                   -> Var
                   -> m (Exp a)
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

intFactors :: forall a m . (Ord a, Floating a, Floating (Const a), IsConst a, MonadPlus m)
           => [(Exp a, Const a)] -> Var -> m (Exp a)
intFactors [] x = pure $ VarE x
intFactors fs x = msum [derivDivides u n x fs | (u, n) <- fs]

derivDivides :: forall a m . (Ord a, Floating a, Floating (Const a), IsConst a, MonadPlus m)
             => Exp a -> Const a -> Var -> [(Exp a, Const a)] -> m (Exp a)
derivDivides u n x fs | freeOf x k =
    if n == -1
    then pure $ k * log u
    else pure $ k * u ** (ConstE (n+1)) / (ConstE (n+1))
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

tableIntegrate :: forall a m . (Eq a, Floating a, Floating (Const a), IsConst a, MonadPlus m)
               => FloatUnop
               -> m (Exp a -> Exp a)
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
