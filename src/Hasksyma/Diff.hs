{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  Hasksyma.Diff
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu
--
-- Construction of symbolic derivative expressions.

module Hasksyma.Diff
  ( diff
  ) where

import           Hasksyma.Const (Const)
import           Hasksyma.Exp   (Exp (DiffE, VarE))

-- | Construct an unevaluated derivative with respect to a variable expression.
--
-- The second argument must be a 'VarE'. Passing any other expression raises an
-- error. Apply 'Hasksyma.Simplify.simplify' to reduce the
-- resulting 'DiffE'.
diff :: (Show a, Floating a, Floating (Const a))
     => Exp a -- ^ Expression to differentiate
     -> Exp a -- ^ Variable expression to differentiate with respect to
     -> Exp a
diff e (VarE x) = DiffE e x
diff _ x        = error $ show x ++ " is not a variable"
