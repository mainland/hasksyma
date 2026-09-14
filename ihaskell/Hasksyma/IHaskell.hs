-- SPDX-License-Identifier: BSD-3-Clause

{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- |
-- Module      : Hasksyma.IHaskell
-- Copyright   : (c) 2023 Drexel University
-- License     : BSD-3-Clause
-- Maintainer  : mainland@drexel.edu
--
-- IHaskell display instances for Hasksyma expressions and constants.
-- Enable the package's @ihaskell@ flag, depend on the public @hasksyma:ihaskell@
-- sublibrary, and import this module to enable notebook display. The core
-- library no longer supplies these instances, and 'displayMath' replaces the
-- former @Hasksyma.LaTeX@ export.
-- Notebook support is available for GHC 9.10 and 9.12. This sublibrary is disabled
-- on GHC 9.13 and later because the released IHaskell dependency requires
-- @ghc <9.13@. The core library also supports GHC 9.14.
module Hasksyma.IHaskell
  ( displayMath,
  )
where

import qualified Data.Text        as Text
import           Hasksyma.Const   (Const)
import           Hasksyma.Exp     (Exp)
import           Hasksyma.LaTeX   (PrettyTeX (tppr))
import           IHaskell.Display (Display, IHaskellDisplay (display))
import qualified IHaskell.Display as IHaskell
import           Text.LaTeX       (Render (render), math)

-- | Render a value as display mathematics in an IHaskell notebook.
displayMath :: PrettyTeX a => a -> IO Display
displayMath = display . IHaskell.latex . Text.unpack . render . math . tppr

instance PrettyTeX a => IHaskellDisplay (Const a) where
  display = displayMath

instance PrettyTeX (Exp a) => IHaskellDisplay (Exp a) where
  display = displayMath
