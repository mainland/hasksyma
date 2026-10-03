{-# LANGUAGE OverloadedStrings #-}

module Test.Root where

import           Control.Monad                   (forM_)
import           Data.Complex                    (Complex (..), magnitude)
import           Test.Hspec
import           Test.HUnit
import           Text.PrettyPrint.Mainland       (prettyCompact)
import           Text.PrettyPrint.Mainland.Class (ppr)

import           Hasksyma.Const
import           Hasksyma.Diff                   (diff)
import           Hasksyma.Eval
import           Hasksyma.Exp
import           Hasksyma.Integrate              (factorize, heuristicIntegrate)
import           Hasksyma.LaTeX                  (tppr)
import           Hasksyma.Simplify               (simplify)

rootTests :: Spec
rootTests = describe "Roots" $ do
    rootSemanticsTests
    it "prints the radicand raised to the reciprocal degree" $
      plain (root 3 8) @?= "8 ** recip 3"
    it "preserves symbolic operand order" $
      plain (root n x) @?= "x ** recip n"
    it "parenthesizes compound operands" $
      plain (root (NumBinopE Add n 1) (NumBinopE Add x 1)) @?=
        "(x + 1) ** recip (n + 1)"
    it "parenthesizes a root used as a power base" $
      plain (NatPowE (root n x) 2) @?= "(x ** recip n) ^ 2"
    it "parenthesizes a root used as a root degree" $
      plain (root (root 2 n) x) @?= "x ** recip (n ** recip 2)"
    it "prints the LaTeX radicand under its degree" $
      latex (root 3 8) `shouldContain` "\\sqrt[3]{8}"
    it "preserves symbolic LaTeX operand order" $
      latex (root n x) `shouldContain` "\\sqrt[n]{x}"
    it "omits the LaTeX degree only for square roots" $
      latex (root 2 x) @?= latex (FloatUnopE Sqrt x)
    it "retains the LaTeX degree when the radicand is two" $
      latex (root 3 2) `shouldContain` "\\sqrt[3]{2}"
    it "keeps nested LaTeX roots in the radicand" $
      latex (root 2 (root 3 x)) `shouldContain` "\\sqrt{\\sqrt[3]{x}}"
  where
    root :: Exp Double -> Exp Double -> Exp Double
    root = FloatBinopE Root

    x, n :: Exp Double
    x = VarE "x"
    n = VarE "n"

    plain :: Exp Double -> String
    plain = prettyCompact . ppr

    latex :: Exp Double -> String
    latex = prettyCompact . ppr . tppr

rootSemanticsTests :: Spec
rootSemanticsTests = do
    it "supports partial application to the degree" $
      floatbinop Root (3 :: Double) 8 @?= 2
    it "evaluates a cube root with the degree first" $
      value (eval (root 3 8)) @?= 2
    it "evaluates negative degrees as reciprocal powers" $
      value (eval (root (-1) 8)) @?= 1/8
    it "preserves exactness and meaning with a rational degree" $ do
      let e = evalexact (root (ConstE (RationalC (1/2))) 8)
      isExactE e @?= True
      value (eval e) @?= 64
    it "normalizes integer and rational degrees to exact exponents" $
      forM_ [(3, 1/3), (-3, -1/3), (ConstE (RationalC (3/2)), 2/3)] $ \(degree, power) ->
        sameExp (simplify (root degree x)) (FracPowE x power) @?= True
    it "normalizes symbolic degrees without reversing the base" $
      simplify (root (VarE "n") x) @?=
        simplify (FloatBinopE Pow x (FracUnopE Recip (VarE "n")))
    it "preserves the floating complex branch" $
      let e = FloatBinopE Root 3 (ConstE (IntegerC (-8))) :: Exp (Complex Double)
      in case eval e of
           ConstE c -> magnitude (fromConst c - (((-8) :+ 0) ** ((1/3) :+ 0))) `shouldSatisfy` (< 1e-12)
           result -> assertFailure (show result)
    it "uses floating power semantics for negative real radicands" $
      value (eval (root 3 (ConstE (IntegerC (-8))))) `shouldSatisfy` isNaN
    it "preserves zero radicands" $
      value (eval (root 3 0)) @?= 0
    it "uses a floating reciprocal for degree zero" $
      value (eval (root 0 8)) @?= 1/0
    it "differentiates with respect to the radicand" $
      simplify (diff (root 3 x) x) @?= simplify (diff (FracPowE x (1/3)) x)
    it "retains roots as intact factors" $
      factorize (root 3 x) @?= [(root 3 x, 1)]
    it "integrates a normalized cube root using its reciprocal degree" $
      case heuristicIntegrate (simplify (root 3 x)) "x" :: [Exp Double] of
        antideriv : _ -> simplify (diff antideriv x) @?= simplify (root 3 x)
        []            -> assertFailure "No antiderivative for the cube root"
  where
    root :: Exp Double -> Exp Double -> Exp Double
    root = FloatBinopE Root

    x :: Exp Double
    x = VarE "x"

    value :: Exp Double -> Double
    value (ConstE c) = fromConst c
    value e          = error (show e)
