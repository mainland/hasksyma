{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      :  Hasksyma.Diff
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Hasksyma.Diff
  ( diff
  ) where

import Hasksyma.Const ( Const )
import Hasksyma.Exp ( Exp(DiffE, VarE) )

diff :: (Show a, Floating a, Floating (Const a)) => Exp a -> Exp a -> Exp a
diff e (VarE x) = DiffE e x
diff _ x        = error $ show x ++ " is not a variable"
