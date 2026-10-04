{-# LANGUAGE OverloadedStrings #-}

module Test.LaTeX (latexTests) where

import           Data.Complex                    (Complex (..))
import           Test.Hspec                      (Spec, describe, it, shouldBe)
import           Text.PrettyPrint.Mainland       (prettyCompact)
import           Text.PrettyPrint.Mainland.Class (ppr)

import           Hasksyma.Const                  (Const (..))
import           Hasksyma.Exp                    (Exp (..))
import           Hasksyma.LaTeX                  (PrettyTeX (tppr))

latexTests :: Spec
latexTests = describe "LaTeX numeric rendering regressions" $ do
    it "retains the sign of negative fractional Float values" $
      latex (-0.5 :: Float) `shouldBe` "$-0.50000$"
    it "retains the sign of negative fractional Double values" $
      latex (-0.5 :: Double) `shouldBe` "$-0.50000$"
    it "retains the sign of an evaluated expression constant" $
      latex (ConstE (Const (-0.5)) :: Exp Double) `shouldBe` "$-0.50000$"
    it "subtracts a negative fractional imaginary component" $
      latex (1 :+ (-0.5) :: Complex Double) `shouldBe` "$1-0.50000i$"
    it "preserves finite integral and fractional rendering" $ do
      latex (-2 :: Double) `shouldBe` "$-2$"
      latex (0.5 :: Double) `shouldBe` "$0.50000$"
      latex (-0.0 :: Double) `shouldBe` "$0$"

latex :: PrettyTeX a => a -> String
latex = prettyCompact . ppr . tppr
