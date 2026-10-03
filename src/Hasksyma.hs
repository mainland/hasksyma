-- |
-- Module      :  Hasksyma
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu
--
-- A convenient entry point for Hasksyma's public core API.
--
-- Import the individual modules when you want tighter control over names, or
-- import this module to get the complete symbolic mathematics interface:
--
-- >>> :set -XOverloadedStrings
-- >>> let x = VarE "x" :: Exp Double
-- >>> simplify (diff (x ^ (2 :: Integer)) x) == 2 * x
-- True

module Hasksyma
  ( module Hasksyma.Condition,
    module Hasksyma.Const,
    module Hasksyma.Diff,
    module Hasksyma.Eval,
    module Hasksyma.Exp,
    module Hasksyma.Integrate,
    module Hasksyma.LaTeX,
    module Hasksyma.Pretty,
    module Hasksyma.Simplify,
    module Hasksyma.Simplify.Checked,
  )
where

import           Hasksyma.Condition
import           Hasksyma.Const
import           Hasksyma.Diff
import           Hasksyma.Eval
import           Hasksyma.Exp
import           Hasksyma.Integrate
import           Hasksyma.LaTeX
import           Hasksyma.Pretty
import           Hasksyma.Simplify
import           Hasksyma.Simplify.Checked
