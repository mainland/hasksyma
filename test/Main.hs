{-# LANGUAGE CPP #-}

-- |
-- Module      :  Main
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Main where

import           Test.Hspec     (Spec, hspec)

import           Test.Condition
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
import           Test.Root
import           Test.Simplify

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    conditionTests
    constTests
    exactConstTests
    evalTests
    simplifyTests
    diffTests
    integrateTests
    rootTests
#if defined(PEVAL)
    powPevalTests
#else
    noPevalTests
#endif
