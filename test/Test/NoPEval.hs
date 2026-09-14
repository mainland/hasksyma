-- SPDX-License-Identifier: BSD-3-Clause

{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : Test.NoPEval
-- Copyright   : (c) 2023 Drexel University
-- License     : BSD-3-Clause
-- Maintainer  : mainland@drexel.edu
module Test.NoPEval (noPevalTests) where

import           Hasksyma.Exp (Exp (ConstE, FracUnopE, NumBinopE, VarE), FracUnop (Recip),
                               NumBinop (Add, Mul))
import           Test.Hspec   (Spec, describe, it)
import           Test.HUnit   ((@?=))

noPevalTests :: Spec
noPevalTests = describe "Expressions without partial evaluation" $ do
  it "preserves addition by zero" $
    (x + 0 :: Exp Double) @?= NumBinopE Add x (ConstE 0)
  it "preserves repeated multiplication" $
    (x * x :: Exp Double) @?= NumBinopE Mul x x
  it "preserves reciprocal applications" $
    (recip x :: Exp Double) @?= FracUnopE Recip x
  where
    x = VarE "x"
