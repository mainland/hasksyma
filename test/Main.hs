{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      :  Main
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Main where

import Data.Complex
import Test.HUnit
import Test.Hspec
import Test.QuickCheck

import Hasksyma.Const

import Test.Const
import Test.Eval
import Test.Exact

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    constTests
    exactConstTests
    evalTests
