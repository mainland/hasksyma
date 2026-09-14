{-# LANGUAGE CPP #-}

-- |
-- Module      :  Main
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Main where

import           Data.Complex
import           Test.Hspec
import           Test.HUnit
import           Test.QuickCheck

import           Hasksyma.Const

import           Test.Const
import           Test.Diff
import           Test.Eval
import           Test.Exact
import           Test.Integrate
#if !defined(PEVAL)
import           Test.NoPEval
#else
import           Test.PEval
#endif
import           Test.Simplify

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    constTests
    exactConstTests
    evalTests
    simplifyTests
    diffTests
    integrateTests
#if defined(PEVAL)
    powPevalTests
#else
    noPevalTests
#endif
