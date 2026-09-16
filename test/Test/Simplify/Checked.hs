{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  Test.Simplify.Checked
-- Copyright   :  (c) 2026 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Simplify.Checked (checkedSimplifyTests) where

import           Control.Monad             (forM_)
import           Data.Complex              (Complex)
import           Test.Hspec                (Spec, describe, it, shouldBe)

import           Hasksyma.Condition
import           Hasksyma.Const            (Const (..), IsConst)
import           Hasksyma.Eval             (evalexact)
import           Hasksyma.Exp
import           Hasksyma.Simplify.Checked

checkedSimplifyTests :: Spec
checkedSimplifyTests = describe "Checked simplification" $ do
    certificateTests
    it "cancels identical differences with replayable evidence" $ do
      let source = NumBinopE Sub x x
      result <- expectRight (simplifyChecked 1 context source)
      sameExp (value result) (ConstE (IntegerC 0)) `shouldBe` True
      expectTrue (sourceDomain result)
      expectTrue (obligations result)
      checkSimplification source result `shouldBe` True
      completion result `shouldBe` NoApplicableRule
    it "retains the excluded zero when cancelling a quotient" $ do
      let source = FracBinopE FDiv x x
      result <- expectRight (simplifyChecked 1 context source)
      sameExp (value result) (ConstE (IntegerC 1)) `shouldBe` True
      expectNonZeroX (sourceDomain result)
      expectTrue (obligations result)
      checkSimplification source result `shouldBe` True
    it "retains singularities inside cancelled differences" $ do
      let inverse = FracUnopE Recip x
      forM_ [inverse, NatPowE inverse 0] $ \operand -> do
        let source = NumBinopE Sub operand operand
        -- Both zero-power children can now rewrite before the subtraction.
        result <- expectRight (simplifyChecked 3 context source)
        sameExp (value result) (ConstE (IntegerC 0)) `shouldBe` True
        expectNonZeroX (sourceDomain result)
        checkSimplification source result `shouldBe` True
    it "retains exclusions already established by the recorded context" $ do
      positiveContext <- expectRight (assuming (positive x) context)
      result <- expectRight (simplifyChecked 1 positiveContext (FracBinopE FDiv x x))
      expectNonZeroX (sourceDomain result)
      decision <- expectRight (decide (contextUsed result) (positive x))
      checkDecision (contextUsed result) (positive x) decision `shouldBe` True
    describe "Checked denominator cancellation" $ do
      it "cancels either numerator factor and retains its nonzero restriction" $
        forM_ [NumBinopE Mul x y, NumBinopE Mul y x] $ \numerator -> do
          let source = FracBinopE FDiv numerator x
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) y `shouldBe` True
          expectNonZeroX (sourceDomain result)
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "cancels either denominator factor while retaining the original product exclusion" $
        forM_ [NumBinopE Mul x y, NumBinopE Mul y x] $ \denominator -> do
          let source = FracBinopE FDiv x denominator
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) (FracUnopE Recip y) `shouldBe` True
          case viewCondition (sourceDomain result) of
            NonZeroView e -> sameExp e denominator `shouldBe` True
            _             -> fail "Expected the original denominator exclusion"
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "reduces exact zero numerators without erasing denominator exclusions" $
        forM_ [IntegerC 0, RationalC 0, Pi 0] $ \zero -> do
          let source = FracBinopE FDiv (ConstE zero) x
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) (ConstE (IntegerC 0)) `shouldBe` True
          expectNonZeroX (sourceDomain result)
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "subtracts natural exponents in signed arithmetic" $
        forM_ [(2, 5, -3), (5, 2, 3), (3, 2, 1), (0, 2, -2)] $ \(n, m, k) -> do
          let source = FracBinopE FDiv (NatPowE x n) (NatPowE x m)
              expected = if k == 1 then x else IntPowE x k
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) expected `shouldBe` True
          checkDomain context source (sourceDomain result) `shouldBe` True
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "combines natural, signed, reciprocal, and bare-base power encodings" $
        forM_ [(NatPowE x 2, IntPowE x 2, ConstE (IntegerC 1)),
               (IntPowE x (-3), NatPowE x 2, IntPowE x (-5)),
               (NatPowE x 2, IntPowE x (-3), IntPowE x 5),
               (IntPowE x (-2), IntPowE x (-3), x),
               (x, NatPowE x 3, IntPowE x (-2)),
               (FracUnopE Recip x, x, IntPowE x (-2)),
               (x, FracUnopE Recip x, IntPowE x 2)] $ \(numerator, denominator, expected) -> do
          let source = FracBinopE FDiv numerator denominator
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) expected `shouldBe` True
          checkDomain context source (sourceDomain result) `shouldBe` True
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "keeps zero-exponent source domains without inventing a nonzero-base condition" $ do
        let denominator = IntPowE x 0
            source = FracBinopE FDiv (NatPowE x 0) denominator
        result <- expectRight (simplifyChecked 1 context source)
        sameExp (value result) (ConstE (IntegerC 1)) `shouldBe` True
        case viewCondition (sourceDomain result) of
          NonZeroView e -> sameExp e denominator `shouldBe` True
          _             -> fail "Expected the original zero-power denominator condition"
        checkSimplification source result `shouldBe` True
      it "preserves exact values across positive, negative, and zero bases" $
        forM_ [-2, -1, 0, 1, 2] $ \base ->
          forM_ [-3 .. 3] $ \n ->
            forM_ [-3 .. 3] $ \m ->
              if base == 0 && (n < 0 || m /= 0) then pure () else do
                let operand = ConstE (IntegerC base) :: Exp Rational
                    source = FracBinopE FDiv (IntPowE operand n) (IntPowE operand m)
                result <- expectRight (simplifyChecked 1 (emptyContext realScalars) source)
                evalexact (value result) `shouldBe` evalexact source
                checkSimplification source result `shouldBe` True
      it "retains nested singularities through cancellation and continuation" $ do
        let inverse = FracUnopE Recip x
            quotient = FracBinopE FDiv (NumBinopE Mul y inverse) y
            source = NumBinopE Sub quotient inverse
        pending <- expectRight (simplifyChecked 1 context source)
        sameExp (value pending) (NumBinopE Sub inverse inverse) `shouldBe` True
        completion pending `shouldBe` BudgetExhausted
        checkSimplification source pending `shouldBe` True
        result <- expectRight (continueChecked 1 pending)
        sameExp (value result) (ConstE (IntegerC 0)) `shouldBe` True
        case viewCondition (sourceDomain result) of
          ConjunctionView [dx, dy] -> do
            expectNonZeroX dx
            case viewCondition dy of
              NonZeroView e -> sameExp e y `shouldBe` True
              _             -> fail "Expected the cancelled factor exclusion"
          _ -> fail "Expected both original exclusions"
        checkSimplification source result `shouldBe` True
      it "retains conditional obligations when a later denominator factor cancels" $ do
        let source = FracBinopE FDiv (NumBinopE Mul (NumUnopE Abs x) y) x
        pending <- expectRight (simplifyConditional 1 context source)
        result <- expectRight (continueChecked 1 pending)
        sameExp (value result) y `shouldBe` True
        expectNonZeroX (sourceDomain result)
        expectNonNegative x (obligations result)
        checkSimplification source result `shouldBe` True
      it "leaves mismatched factors and bases intact" $
        forM_ [FracBinopE FDiv (NumBinopE Mul x (VarE "z")) y,
               FracBinopE FDiv x (NumBinopE Mul y (VarE "z")),
               FracBinopE FDiv (NatPowE x 2) (IntPowE y 3)] $ \source -> do
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) source `shouldBe` True
          completion result `shouldBe` NoApplicableRule
          checkSimplification source result `shouldBe` True
      it "validates all operands and rejects known zero denominators before cancellation" $ do
        forM_ [FracBinopE FDiv (ConstE (IntegerC 0)) (ConstE (IntegerC 0)),
               FracBinopE FDiv (NumBinopE Mul Undefined x) x,
               FracBinopE FDiv (IntPowE (ConstE (IntegerC 0)) (-1)) x] $ \source ->
          failure (simplifyChecked 1 context source) `shouldBe` Just EmptySourceDomain
        forM_ [FracBinopE FDiv (ConstE (IntegerC 0)) (FloatUnopE Log x),
               FracBinopE FDiv (FracPowE x 2) (FracPowE x 3)] $ \source ->
          failure (simplifyChecked 1 context source)
            `shouldBe` Just (ConditionFailure UnsupportedOperation)
    describe "Checked integral-power laws" $ do
      it "combines products across natural, signed, reciprocal, and bare encodings" $
        forM_ [(NatPowE x 2, NatPowE x 3, NatPowE x 5),
               (IntPowE x (-2), NatPowE x 2, ConstE (IntegerC 1)),
               (NatPowE x 3, IntPowE x (-2), x),
               (IntPowE x (-2), IntPowE x (-3), IntPowE x (-5)),
               (FracUnopE Recip x, x, ConstE (IntegerC 1)),
               (x, FracUnopE Recip x, ConstE (IntegerC 1)),
               (FracUnopE Recip x, NatPowE x 3, IntPowE x 2),
               (NatPowE x 3, FracUnopE Recip x, IntPowE x 2),
               (x, x, NatPowE x 2)] $ \(left, right, expected) -> do
          let source = NumBinopE Mul left right
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) expected `shouldBe` True
          checkDomain context source (sourceDomain result) `shouldBe` True
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "retains the excluded zero after negative powers cancel" $ do
        let source = NumBinopE Mul (IntPowE x (-2)) (NatPowE x 2)
        result <- expectRight (simplifyChecked 1 context source)
        sameExp (value result) (ConstE (IntegerC 1)) `shouldBe` True
        expectNonZeroX (sourceDomain result)
        checkSimplification source result `shouldBe` True
      it "flattens natural, signed, and reciprocal power layers" $
        forM_ [(NatPowE (NatPowE x 2) 3, NatPowE x 6),
               (NatPowE (IntPowE x (-2)) 3, IntPowE x (-6)),
               (IntPowE (NatPowE x 2) (-3), IntPowE x (-6)),
               (IntPowE (IntPowE x (-2)) (-3), IntPowE x 6),
               (NatPowE (FracUnopE Recip x) 3, IntPowE x (-3)),
               (IntPowE (FracUnopE Recip x) (-3), IntPowE x 3),
               (FracUnopE Recip (NatPowE x 3), IntPowE x (-3)),
               (FracUnopE Recip (IntPowE x (-3)), IntPowE x 3)] $ \(source, expected) -> do
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) expected `shouldBe` True
          checkDomain context source (sourceDomain result) `shouldBe` True
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "retains both original exclusions when two negative power layers cancel" $ do
        let inner = IntPowE x (-2)
            source = IntPowE inner (-3)
        result <- expectRight (simplifyChecked 1 context source)
        sameExp (value result) (IntPowE x 6) `shouldBe` True
        case viewCondition (sourceDomain result) of
          ConjunctionView [dx, di] -> do
            expectNonZeroX dx
            case viewCondition di of
              NonZeroView e -> sameExp e inner `shouldBe` True
              _             -> fail "Expected the inner-power exclusion"
          _ -> fail "Expected both original exclusions"
        checkSimplification source result `shouldBe` True
      it "retains strict operand domains when an outer zero power drops its base" $ do
        forM_ [NatPowE (IntPowE x (-2)) 0, IntPowE (IntPowE x (-2)) 0] $ \source -> do
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) (ConstE (IntegerC 1)) `shouldBe` True
          expectNonZeroX (sourceDomain result)
          checkSimplification source result `shouldBe` True
      it "does not exclude zero from products and nesting of nonnegative powers" $
        forM_ [NumBinopE Mul (NatPowE x 0) (NatPowE x 0),
               NatPowE (NatPowE x 0) 0,
               NatPowE (IntPowE x 0) 3] $ \source -> do
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) (ConstE (IntegerC 1)) `shouldBe` True
          expectTrue (sourceDomain result)
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "supports natural products and nesting without a Fractional carrier" $ do
        let z = VarE "z" :: Exp Integer
        forM_ [(NumBinopE Mul (NatPowE z 2) z, NatPowE z 3),
               (NatPowE (NatPowE z 2) 3, NatPowE z 6)] $ \(source, expected) -> do
          result <- expectRight (simplifyChecked 1 (emptyContext realScalars) source)
          sameExp (value result) expected `shouldBe` True
          checkSimplification source result `shouldBe` True
      it "preserves exact products and nested powers on their defined domains" $
        forM_ [-2, -1, 0, 1, 2] $ \base ->
          forM_ [-3 .. 3] $ \n ->
            forM_ [-3 .. 3] $ \m -> do
              let operand = ConstE (IntegerC base) :: Exp Rational
                  multiplied = NumBinopE Mul (IntPowE operand n) (IntPowE operand m)
                  nested = IntPowE (IntPowE operand n) m
                  sources = [multiplied | base /= 0 || (n >= 0 && m >= 0)] ++
                            [nested | base /= 0 || (n >= 0 && (n == 0 || m >= 0))]
              forM_ sources $ \source -> do
                result <- expectRight (simplifyChecked 2 (emptyContext realScalars) source)
                evalexact (value result) `shouldBe` evalexact source
                checkSimplification source result `shouldBe` True
      it "shares a budget across nested powers and a later product" $ do
        let source = NumBinopE Mul (IntPowE (IntPowE x (-2)) (-3)) (IntPowE x (-6))
        pending <- expectRight (simplifyChecked 0 context source)
        sameExp (value pending) source `shouldBe` True
        completion pending `shouldBe` BudgetExhausted
        child <- expectRight (continueChecked 1 pending)
        sameExp (value child) (NumBinopE Mul (IntPowE x 6) (IntPowE x (-6))) `shouldBe` True
        result <- expectRight (continueChecked 1 child)
        sameExp (value result) (ConstE (IntegerC 1)) `shouldBe` True
        checkDomain context source (sourceDomain result) `shouldBe` True
        checkSimplification source result `shouldBe` True
      it "retains conditional obligations through power cancellation" $ do
        let source = NumBinopE Mul (NumUnopE Abs x) (FracUnopE Recip x)
        pending <- expectRight (simplifyConditional 1 context source)
        result <- expectRight (continueChecked 1 pending)
        sameExp (value result) (ConstE (IntegerC 1)) `shouldBe` True
        expectNonZeroX (sourceDomain result)
        expectNonNegative x (obligations result)
        checkSimplification source result `shouldBe` True
      it "leaves different bases and single power layers unchanged" $
        forM_ [NumBinopE Mul (IntPowE x (-2)) (NatPowE y 2),
               NatPowE x 3, IntPowE x (-2), FracUnopE Recip x] $ \source -> do
          result <- expectRight (simplifyChecked 2 context source)
          sameExp (value result) source `shouldBe` True
          completion result `shouldBe` NoApplicableRule
          checkSimplification source result `shouldBe` True
      it "validates erased operands and rejects unsupported power semantics" $ do
        forM_ [NatPowE (IntPowE Undefined 2) 0,
               IntPowE (IntPowE (ConstE (IntegerC 0)) (-2)) (-3)] $ \source ->
          failure (simplifyChecked 1 context source) `shouldBe` Just EmptySourceDomain
        forM_ [NatPowE (FracPowE x (1/2)) 2,
               NumBinopE Mul (FracPowE x (1/2)) (FracPowE x (-1/2))] $ \source ->
          failure (simplifyChecked 1 context source)
            `shouldBe` Just (ConditionFailure UnsupportedOperation)
    describe "Proved absolute-value rewrites" $ do
      it "uses a nonnegative assumption or its positive strengthening" $
        forM_ [nonNegative x, positive x] $ \premise -> do
          assumptions <- expectRight (assuming premise context)
          let source = NumUnopE Abs x
          result <- expectRight (simplifyChecked 1 assumptions source)
          sameExp (value result) x `shouldBe` True
          expectTrue (sourceDomain result)
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "uses intrinsic nonnegativity without an explicit assumption" $
        forM_ [IntegerC 0, RationalC (1/3), Pi 1] $ \constant -> do
          let source = NumUnopE Abs (ConstE constant)
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) (ConstE constant) `shouldBe` True
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "does not infer a sign from definedness or nonzero" $
        forM_ [trueCondition, defined x, nonZero x, positive y] $ \premise -> do
          assumptions <- expectRight (assuming premise context)
          let source = NumUnopE Abs x
          result <- expectRight (simplifyChecked 1 assumptions source)
          sameExp (value result) source `shouldBe` True
          expectTrue (obligations result)
          completion result `shouldBe` NoApplicableRule
          checkSimplification source result `shouldBe` True
      it "leaves a refuted nonnegativity premise unreduced" $ do
        let source = NumUnopE Abs (ConstE (IntegerC (-1)))
        result <- expectRight (simplifyChecked 1 context source)
        sameExp (value result) source `shouldBe` True
        expectTrue (obligations result)
        checkSimplification source result `shouldBe` True
      it "retains a singular source domain after using a sign assumption" $ do
        let inverse = FracUnopE Recip x
            source = NumUnopE Abs inverse
        assumptions <- expectRight (assuming (nonNegative inverse) context)
        result <- expectRight (simplifyChecked 1 assumptions source)
        sameExp (value result) inverse `shouldBe` True
        expectNonZeroX (sourceDomain result)
        expectTrue (obligations result)
        checkSimplification source result `shouldBe` True
      it "retains premise evidence through traversal and continuation" $ do
        assumptions <- expectRight (assuming (positive x) context)
        let source = NumBinopE Sub (NumUnopE Abs x) x
        pending <- expectRight (simplifyChecked 0 assumptions source)
        completion pending `shouldBe` BudgetExhausted
        child <- expectRight (continueChecked 1 pending)
        sameExp (value child) (NumBinopE Sub x x) `shouldBe` True
        checkSimplification source child `shouldBe` True
        result <- expectRight (continueChecked 1 child)
        sameExp (value result) (ConstE (IntegerC 0)) `shouldBe` True
        expectTrue (obligations result)
        checkSimplification source result `shouldBe` True
    describe "Conditional absolute-value rewrites" $ do
      it "records an unknown sign separately from the source domain and context" $ do
        let source = NumUnopE Abs x
        result <- expectRight (simplifyConditional 1 context source)
        sameExp (value result) x `shouldBe` True
        expectTrue (sourceDomain result)
        expectNonNegative x (obligations result)
        decision <- expectRight (decide (contextUsed result) (nonNegative x))
        case decision of
          Unknown -> pure ()
          _       -> fail "An obligation must not become a caller assumption"
        checkSimplification source result `shouldBe` True
      it "uses proved premises without additional obligations" $
        forM_ [nonNegative x, positive x] $ \premise -> do
          assumptions <- expectRight (assuming premise context)
          let source = NumUnopE Abs x
          result <- expectRight (simplifyConditional 1 assumptions source)
          sameExp (value result) x `shouldBe` True
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "does not introduce a refuted sign requirement" $ do
        let source = NumUnopE Abs (ConstE (IntegerC (-1)))
        result <- expectRight (simplifyConditional 1 context source)
        sameExp (value result) source `shouldBe` True
        expectTrue (obligations result)
        completion result `shouldBe` NoApplicableRule
        checkSimplification source result `shouldBe` True
      it "keeps exact source exclusions separate from sufficient sign obligations" $ do
        let inverse = FracUnopE Recip x
            source = NumUnopE Abs inverse
        result <- expectRight (simplifyConditional 1 context source)
        sameExp (value result) inverse `shouldBe` True
        expectNonZeroX (sourceDomain result)
        expectNonNegative inverse (obligations result)
        checkSimplification source result `shouldBe` True
      it "adds no obligations when the budget prevents a conditional step" $ do
        let source = NumUnopE Abs x
        pending <- expectRight (simplifyConditional 0 context source)
        sameExp (value pending) source `shouldBe` True
        expectTrue (obligations pending)
        completion pending `shouldBe` BudgetExhausted
        checkSimplification source pending `shouldBe` True
        result <- expectRight (continueChecked 1 pending)
        sameExp (value result) source `shouldBe` True
        expectTrue (obligations result)
        completion result `shouldBe` NoApplicableRule
        checkSimplification source result `shouldBe` True
      it "reuses an existing obligation in a checked continuation without duplication" $ do
        let source = NumBinopE Add (NumUnopE Abs x) (NumUnopE Abs x)
        pending <- expectRight (simplifyConditional 1 context source)
        sameExp (value pending) (NumBinopE Add x (NumUnopE Abs x)) `shouldBe` True
        expectNonNegative x (obligations pending)
        completion pending `shouldBe` BudgetExhausted
        checkSimplification source pending `shouldBe` True
        result <- expectRight (continueChecked 1 pending)
        sameExp (value result) (NumBinopE Add x x) `shouldBe` True
        expectNonNegative x (obligations result)
        completion result `shouldBe` NoApplicableRule
        checkSimplification source result `shouldBe` True
      it "requires conditional continuation to add a distinct obligation" $ do
        let source = NumBinopE Add (NumUnopE Abs x) (NumUnopE Abs y)
        pending <- expectRight (simplifyConditional 1 context source)
        checked <- expectRight (continueChecked 2 pending)
        sameExp (value checked) (NumBinopE Add x (NumUnopE Abs y)) `shouldBe` True
        expectNonNegative x (obligations checked)
        completion checked `shouldBe` NoApplicableRule
        checkSimplification source checked `shouldBe` True
        result <- expectRight (continueConditional 1 checked)
        sameExp (value result) (NumBinopE Add x y) `shouldBe` True
        case viewCondition (obligations result) of
          ConjunctionView [hx, hy] -> do
            expectNonNegative x hx
            expectNonNegative y hy
          _ -> fail "Expected both obligations in declaration order"
        checkSimplification source result `shouldBe` True
      it "retains obligations and source exclusions after the value becomes constant" $ do
        let inverse = FracUnopE Recip x
            operand = NumUnopE Abs inverse
            source = NumBinopE Sub operand operand
        pending <- expectRight (simplifyConditional 1 context source)
        result <- expectRight (continueChecked 2 pending)
        sameExp (original result) source `shouldBe` True
        sameExp (value result) (ConstE (IntegerC 0)) `shouldBe` True
        expectNonZeroX (sourceDomain result)
        expectNonNegative inverse (obligations result)
        checkSimplification source result `shouldBe` True
      it "can explicitly narrow a previously completed checked result" $ do
        let source = NumUnopE Abs x
        checked <- expectRight (simplifyChecked 1 context source)
        completion checked `shouldBe` NoApplicableRule
        result <- expectRight (continueConditional 1 checked)
        sameExp (value result) x `shouldBe` True
        expectNonNegative x (obligations result)
        checkSimplification source result `shouldBe` True
      it "validates the entire input before introducing any condition" $ do
        let source = NumBinopE Add (NumUnopE Abs x) (FloatUnopE Log y)
        failure (simplifyConditional 1 context source)
          `shouldBe` Just (ConditionFailure UnsupportedOperation)
        failure (simplifyConditional 1 context (NumUnopE Abs Undefined))
          `shouldBe` Just EmptySourceDomain
      it "rejects negative conditional budgets" $ do
        failure (simplifyConditional (-1) context x) `shouldBe` Just InvalidBudget
        result <- expectRight (simplifyConditional 0 context x)
        failure (continueConditional (-1) result) `shouldBe` Just InvalidBudget
    describe "Checked trigonometric identity" $ do
      it "handles both term orders and integral square encodings" $
        forM_ [(`NatPowE` 2), (`IntPowE` 2)] $ \squareSin ->
          forM_ [(`NatPowE` 2), (`IntPowE` 2)] $ \squareCos -> do
            let s = squareSin (FloatUnopE Sin x)
                c = squareCos (FloatUnopE Cos x)
            forM_ [NumBinopE Add s c, NumBinopE Add c s] $ \source -> do
              result <- expectRight (simplifyChecked 1 context source)
              sameExp (value result) (ConstE (IntegerC 1)) `shouldBe` True
              expectTrue (sourceDomain result)
              expectTrue (obligations result)
              checkSimplification source result `shouldBe` True
      it "retains singularities in the shared argument" $ do
        let inverse = FracUnopE Recip x
            source = NumBinopE Add (NatPowE (FloatUnopE Sin inverse) 2)
                                   (IntPowE (FloatUnopE Cos inverse) 2)
        result <- expectRight (simplifyChecked 1 context source)
        sameExp (value result) (ConstE (IntegerC 1)) `shouldBe` True
        expectNonZeroX (sourceDomain result)
        expectTrue (obligations result)
        checkSimplification source result `shouldBe` True
      it "replays the identity under a parent after simplifying its arguments" $ do
        let quotient = FracBinopE FDiv x x
            source = NumUnopE Neg (NumBinopE Add (NatPowE (FloatUnopE Sin quotient) 2)
                                                (NatPowE (FloatUnopE Cos quotient) 2))
        pending <- expectRight (simplifyChecked 2 context source)
        completion pending `shouldBe` BudgetExhausted
        checkSimplification source pending `shouldBe` True
        result <- expectRight (continueChecked 1 pending)
        sameExp (value result) (NumUnopE Neg (ConstE (IntegerC 1))) `shouldBe` True
        expectNonZeroX (sourceDomain result)
        completion result `shouldBe` NoApplicableRule
        checkSimplification source result `shouldBe` True
      it "leaves mismatched functions, arguments, and exponents unchanged" $ do
        let sine = FloatUnopE Sin x
            cosine = FloatUnopE Cos x
        forM_ [NumBinopE Add (NatPowE sine 2) (NatPowE (FloatUnopE Cos y) 2),
               NumBinopE Add (NatPowE sine 2) (NatPowE sine 2),
               NumBinopE Add (NatPowE cosine 2) (NatPowE cosine 2),
               NumBinopE Add (NatPowE sine 3) (IntPowE cosine 2),
               NumBinopE Add (NatPowE sine 2) (IntPowE cosine (-2))] $ \source -> do
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) source `shouldBe` True
          completion result `shouldBe` NoApplicableRule
          checkSimplification source result `shouldBe` True
      it "does not match an exact named constant with its floating approximation" $ do
        let p = ConstE (Pi 1)
            q = ConstE (RationalC (toRational (pi :: Double)))
            source = NumBinopE Add (NatPowE (FloatUnopE Sin p) 2) (NatPowE (FloatUnopE Cos q) 2)
        result <- expectRight (simplifyChecked 1 context source)
        sameExp (value result) source `shouldBe` True
        checkSimplification source result `shouldBe` True
      it "rejects undefined arguments and unsupported power forms" $ do
        let source = NumBinopE Add (NatPowE (FloatUnopE Sin Undefined) 2)
                                   (NatPowE (FloatUnopE Cos Undefined) 2)
        failure (simplifyChecked 1 context source) `shouldBe` Just EmptySourceDomain
        let fractional = NumBinopE Add (FracPowE (FloatUnopE Sin x) 2)
                                       (NatPowE (FloatUnopE Cos x) 2)
        failure (simplifyChecked 1 context fractional)
          `shouldBe` Just (ConditionFailure UnsupportedOperation)
    describe "Further root identities" $ do
      it "cancels opposite terms in either order without losing singularities" $ do
        let inverse = FracUnopE Recip x
        forM_ [NumBinopE Add inverse (NumUnopE Neg inverse),
               NumBinopE Add (NumUnopE Neg inverse) inverse] $ \source -> do
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) (ConstE (IntegerC 0)) `shouldBe` True
          expectNonZeroX (sourceDomain result)
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "reduces exact zero products in either order while retaining singularities" $
        forM_ [IntegerC 0, RationalC 0, Pi 0] $ \zero -> do
          let inverse = FracUnopE Recip x
          forM_ [NumBinopE Mul (ConstE zero) inverse,
                 NumBinopE Mul inverse (ConstE zero)] $ \source -> do
            result <- expectRight (simplifyChecked 1 context source)
            sameExp (value result) (ConstE (IntegerC 0)) `shouldBe` True
            expectNonZeroX (sourceDomain result)
            expectTrue (obligations result)
            checkSimplification source result `shouldBe` True
      it "cancels nested reciprocals while retaining the full original domain" $ do
        let source = FracUnopE Recip (FracUnopE Recip x)
        result <- expectRight (simplifyChecked 1 context source)
        sameExp (value result) x `shouldBe` True
        checkDomain context source (sourceDomain result) `shouldBe` True
        case viewCondition (sourceDomain result) of
          ConjunctionView [first, second] -> do
            expectNonZeroX first
            case viewCondition second of
              NonZeroView e -> sameExp e (FracUnopE Recip x) `shouldBe` True
              _             -> fail "Expected the reciprocal restriction"
          _ -> fail "Expected both original reciprocal restrictions"
        expectTrue (obligations result)
        checkSimplification source result `shouldBe` True
      it "replays multiple reciprocal cancellations across a budget boundary" $ do
        let source = iterate (FracUnopE Recip) x !! 4
        pending <- expectRight (simplifyChecked 1 context source)
        sameExp (value pending) (FracUnopE Recip (FracUnopE Recip x)) `shouldBe` True
        completion pending `shouldBe` BudgetExhausted
        checkSimplification source pending `shouldBe` True
        result <- expectRight (continueChecked 1 pending)
        sameExp (original result) source `shouldBe` True
        sameExp (value result) x `shouldBe` True
        checkDomain context source (sourceDomain result) `shouldBe` True
        completion result `shouldBe` NoApplicableRule
        checkSimplification source result `shouldBe` True
        checkSimplification (value pending) result `shouldBe` False
      it "rejects known undefined operands before erasing them" $
        forM_ [NumBinopE Mul (ConstE (IntegerC 0)) Undefined,
               NumBinopE Add Undefined (NumUnopE Neg Undefined),
               FracUnopE Recip (FracUnopE Recip (ConstE (IntegerC 0)))] $ \source ->
          failure (simplifyChecked 1 context source) `shouldBe` Just EmptySourceDomain
      it "rejects uninterpreted operands before erasing them" $ do
        let source = NumBinopE Mul (ConstE (IntegerC 0)) (FloatUnopE Log x)
        failure (simplifyChecked 1 context source)
          `shouldBe` Just (ConditionFailure UnsupportedOperation)
      it "leaves unmatched opposites and nonzero products unchanged" $
        forM_ [NumBinopE Add x (NumUnopE Neg y),
               NumBinopE Add (NumUnopE Neg y) x,
               NumBinopE Mul (ConstE (RationalC (1/100))) x,
               FracUnopE Recip x] $ \source -> do
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) source `shouldBe` True
          completion result `shouldBe` NoApplicableRule
          checkSimplification source result `shouldBe` True
    it "reports known empty domains before cancellation, even with zero budget" $
      forM_ [0, 1] $ \budget ->
        forM_ [NumBinopE Sub Undefined Undefined,
               FracBinopE FDiv (ConstE (IntegerC 0)) (ConstE (IntegerC 0))] $ \source ->
          failure (simplifyChecked budget context source) `shouldBe` Just EmptySourceDomain
    it "validates cancelled syntax before applying an identity" $
      forM_ [FloatUnopE Log x, ConstE (Const 2)] $ \operand -> do
        let expected = case operand of
              ConstE _ -> UnsupportedConstant
              _        -> UnsupportedOperation
        failure (simplifyChecked 1 context (NumBinopE Sub operand operand))
          `shouldBe` Just (ConditionFailure expected)
    it "rejects calculus nodes even when their difference would cancel" $ do
      let operand = DiffE x "x"
      failure (simplifyChecked 1 context (NumBinopE Sub operand operand))
        `shouldBe` Just (ConditionFailure UnsupportedOperation)
    it "does not equate different operands" $
      forM_ [NumBinopE Sub x y, FracBinopE FDiv x y] $ \source -> do
        result <- expectRight (simplifyChecked 5 context source)
        sameExp (value result) source `shouldBe` True
        checkSimplification source result `shouldBe` True
        completion result `shouldBe` NoApplicableRule
    describe "Recursive checked traversal" $ do
      it "rewrites children under every supported unary constructor" $ do
        let child = FracBinopE FDiv x x
        forM_ [NumUnopE Neg, NumUnopE Abs, NumUnopE Signum,
               FracUnopE Recip, FloatUnopE Sin, FloatUnopE Cos,
               (`NatPowE` 0), (`NatPowE` 3), (`IntPowE` (-2))] $ \wrap -> do
          let source = wrap child
          result <- expectRight (simplifyChecked 1 context source)
          sameExp (value result) (wrap (ConstE (IntegerC 1))) `shouldBe` True
          checkDomain context source (sourceDomain result) `shouldBe` True
          expectTrue (obligations result)
          checkSimplification source result `shouldBe` True
      it "rewrites either binary child while retaining the other operand" $ do
        let child = FracBinopE FDiv x x
        forM_ [NumBinopE Add, NumBinopE Sub, NumBinopE Mul, FracBinopE FDiv] $ \combine ->
          forM_ [(combine child y, combine (ConstE (IntegerC 1)) y),
                 (combine y child, combine y (ConstE (IntegerC 1)))] $ \(source, expected) -> do
            result <- expectRight (simplifyChecked 1 context source)
            sameExp (value result) expected `shouldBe` True
            checkSimplification source result `shouldBe` True
      it "uses one shared budget and visits the left child first" $ do
        let source = NumBinopE Add (NumBinopE Sub x x) (NumBinopE Sub y y)
        pending <- expectRight (simplifyChecked 1 context source)
        sameExp (value pending) (NumBinopE Add (ConstE (IntegerC 0)) (NumBinopE Sub y y))
          `shouldBe` True
        completion pending `shouldBe` BudgetExhausted
        checkSimplification source pending `shouldBe` True
        result <- expectRight (continueChecked 1 pending)
        sameExp (value result) (NumBinopE Add (ConstE (IntegerC 0)) (ConstE (IntegerC 0)))
          `shouldBe` True
        completion result `shouldBe` NoApplicableRule
        checkSimplification source result `shouldBe` True
      it "applies a newly enabled parent rule after its child" $ do
        let inverse = FracUnopE Recip x
            source = NumBinopE Mul (NumBinopE Sub inverse inverse) y
        pending <- expectRight (simplifyChecked 1 context source)
        sameExp (value pending) (NumBinopE Mul (ConstE (IntegerC 0)) y) `shouldBe` True
        completion pending `shouldBe` BudgetExhausted
        result <- expectRight (continueChecked 1 pending)
        sameExp (value result) (ConstE (IntegerC 0)) `shouldBe` True
        expectNonZeroX (sourceDomain result)
        checkSimplification source result `shouldBe` True
      it "replays a path through different operators without changing their parameters" $ do
        let inverse = FracUnopE Recip x
            wrap e = NumBinopE Add y (NatPowE (FloatUnopE Cos (IntPowE e 3)) 5)
            source = wrap (NumBinopE Sub inverse inverse)
        result <- expectRight (simplifyChecked 1 context source)
        sameExp (value result) (wrap (ConstE (IntegerC 0))) `shouldBe` True
        expectNonZeroX (sourceDomain result)
        checkSimplification source result `shouldBe` True
        checkSimplification (NumBinopE Add x (NatPowE (FloatUnopE Cos (IntPowE (NumBinopE Sub inverse inverse) 3)) 5)) result
          `shouldBe` False
      it "reports a pending child rewrite even when the root has no rule" $ do
        let source = FloatUnopE Sin (NumBinopE Sub x x)
        result <- expectRight (simplifyChecked 0 context source)
        sameExp (value result) source `shouldBe` True
        completion result `shouldBe` BudgetExhausted
        checkSimplification source result `shouldBe` True
      it "validates the entire source before any child rewrite" $
        forM_ [FloatUnopE Log y, DiffE y "y", IntE Nothing y "y"] $ \unsupported -> do
          let source = NumBinopE Add (NumBinopE Sub x x) unsupported
          failure (simplifyChecked 1 context source)
            `shouldBe` Just (ConditionFailure UnsupportedOperation)
    it "preserves an unfinished result and resumes without losing its source" $ do
      let source = FracBinopE FDiv x x
      pending <- expectRight (simplifyChecked 0 context source)
      sameExp (value pending) source `shouldBe` True
      completion pending `shouldBe` BudgetExhausted
      checkSimplification source pending `shouldBe` True
      result <- expectRight (continueChecked 1 pending)
      again <- expectRight (continueChecked 1 result)
      forM_ [result, again] $ \r -> do
        sameExp (original r) source `shouldBe` True
        sameExp (value r) (ConstE (IntegerC 1)) `shouldBe` True
        expectNonZeroX (sourceDomain r)
        expectTrue (obligations r)
        completion r `shouldBe` NoApplicableRule
        checkSimplification source r `shouldBe` True
    it "reports completion without spending a budget when no rule applies" $ do
      result <- expectRight (simplifyChecked 0 context x)
      completion result `shouldBe` NoApplicableRule
      checkSimplification x result `shouldBe` True
    it "rejects a negative initial or continuation budget" $ do
      failure (simplifyChecked (-1) context x) `shouldBe` Just InvalidBudget
      result <- expectRight (simplifyChecked 0 context x)
      failure (continueChecked (-1) result) `shouldBe` Just InvalidBudget
    it "rejects a proof for another source even when the answers agree" $ do
      result <- expectRight (simplifyChecked 1 context (NumBinopE Sub x x))
      checkSimplification (NumBinopE Sub y y) result `shouldBe` False
      checkSimplification (value result) result `shouldBe` False
    it "supports real interpretation independently of numerical carrier ordering" $ do
      let z = VarE "z" :: Exp (Complex Double)
          source = FracBinopE FDiv z z
      result <- expectRight (simplifyChecked 1 (emptyContext realScalars) source)
      sameExp (value result) (ConstE (IntegerC 1)) `shouldBe` True
      checkSimplification source result `shouldBe` True
  where
    context :: Context Double
    context = emptyContext realScalars

    x, y :: Exp Double
    x = VarE "x"
    y = VarE "y"

    expectNonZeroX condition = case viewCondition condition of
      NonZeroView e -> sameExp e x `shouldBe` True
      _             -> fail "Expected the retained nonzero restriction"

expectRight :: Show e => Either e a -> IO a
expectRight = either (fail . show) pure

failure :: Either e a -> Maybe e
failure = either Just (const Nothing)

expectTrue :: Condition a -> IO ()
expectTrue condition = case viewCondition condition of
    TruthView True -> pure ()
    _              -> fail "Expected no additional restriction"

expectNonNegative :: (Eq a, IsConst a) => Exp a -> Condition a -> IO ()
expectNonNegative expected condition = case viewCondition condition of
    NonNegativeView e -> sameExp e expected `shouldBe` True
    _                 -> fail "Expected a nonnegativity obligation"

-- Exercise only the public certificate API, including caller-built claims.
certificateTests :: Spec
certificateTests = describe "Public simplification certificates" $ do
    forM_ identities $ \(rule, source, target) -> do
      it ("replays a caller-built " ++ show rule ++ " step") $ do
        result <- candidate source target (Derivation [Step [] rule source target])
        checkSimplification source result `shouldBe` True
      it ("rejects an incorrect result for " ++ show rule) $ do
        let wrong = ConstE (IntegerC 37)
        result <- candidate source wrong (Derivation [Step [] rule source wrong])
        checkSimplification source result `shouldBe` False
    it "exposes the path, rule, and whole expressions of generated steps" $ do
      let source = NumUnopE Neg (FracBinopE FDiv x x)
          target = NumUnopE Neg one
      result <- expectRight (simplifyChecked 1 context source)
      case derivation result of
        Derivation [Step [Operand] CancelQuotient before after] -> do
          sameExp before source `shouldBe` True
          sameExp after target `shouldBe` True
        _ -> fail "Expected a quotient cancellation under negation"
    it "rejects altered record fields and refuses to continue them" $ do
      let source = FracBinopE FDiv x x
      result <- expectRight (simplifyChecked 1 context source)
      forM_ [result { original = x }, result { value = x },
             result { sourceDomain = trueCondition },
             result { obligations = nonNegative x },
             result { derivation = Derivation [] }] $ \bad -> do
        checkSimplification source bad `shouldBe` False
        failure (continueChecked 1 bad) `shouldBe` Just InvalidSimplification
        failure (continueConditional 1 bad) `shouldBe` Just InvalidSimplification
    it "rejects a mismatched rule even when the final expression is correct" $ do
      let source = FracBinopE FDiv x x
      result <- candidate source one (Derivation [Step [] CancelDifference source one])
      checkSimplification source result `shouldBe` False
    it "rejects invalid paths and changes outside the selected operand" $ do
      let source = NumBinopE Add (FracBinopE FDiv x x) (NatPowE y 2)
          target = NumBinopE Add one (NatPowE y 2)
      forM_ [([], target), ([Operand], target), ([RightOperand], target),
             ([LeftOperand, Operand], target),
             ([LeftOperand], NumBinopE Add one (NatPowE y 3)),
             ([LeftOperand], NumBinopE Sub one (NatPowE y 2))] $ \(path, after) -> do
        result <- candidate source after (Derivation [Step path CancelQuotient source after])
        checkSimplification source result `shouldBe` False
    it "rejects missing, reordered, and duplicated steps" $ do
      let source = NumBinopE Add (NumBinopE Sub x x) (NumBinopE Sub y y)
      result <- expectRight (simplifyChecked 2 context source)
      case derivation result of
        Derivation [first, second] ->
          forM_ [[first], [second], [second, first], [first, first, second]] $ \steps ->
            checkSimplification source (result { derivation = Derivation steps }) `shouldBe` False
        _ -> fail "Expected two difference cancellations"
    it "rejects missing obligations and reuse before declaration" $ do
      let source = NumUnopE Abs x
      result <- expectRight (simplifyConditional 1 context source)
      checkSimplification source (result { obligations = trueCondition }) `shouldBe` False
      checkSimplification source (result
        { derivation = Derivation [Step [] UseNonNegativeAbs source x] }) `shouldBe` False
    it "replays obligation reuse and rejects reuse for a different operand" $ do
      let source = NumBinopE Add (NumUnopE Abs x) (NumUnopE Abs x)
          middle = NumBinopE Add x (NumUnopE Abs x)
          target = NumBinopE Add x x
          proof = Derivation [Step [LeftOperand] AssumeNonNegativeAbs source middle,
                              Step [RightOperand] UseNonNegativeAbs middle target]
      result <- candidate source target proof
      checkSimplification source (result { obligations = nonNegative x }) `shouldBe` True
      let otherSource = NumBinopE Add (NumUnopE Abs x) (NumUnopE Abs y)
          otherMiddle = NumBinopE Add x (NumUnopE Abs y)
          otherTarget = NumBinopE Add x y
          otherProof = Derivation [Step [LeftOperand] AssumeNonNegativeAbs otherSource otherMiddle,
                                   Step [RightOperand] UseNonNegativeAbs otherMiddle otherTarget]
      other <- candidate otherSource otherTarget otherProof
      checkSimplification otherSource (other { obligations = nonNegative x }) `shouldBe` False
    it "binds premise evidence to its actual operand and recorded context" $ do
      positiveContext <- expectRight (assuming (positive x) context)
      decision <- expectRight (decide positiveContext (nonNegative x))
      case decision of
        Proved evidence -> do
          let source = NumUnopE Abs x
          result <- candidate source x (Derivation [Step [] (NonNegativeAbs evidence) source x])
          checkSimplification source (result { contextUsed = positiveContext }) `shouldBe` True
          checkSimplification source result `shouldBe` False
          let otherSource = NumUnopE Abs y
          other <- candidate otherSource y
            (Derivation [Step [] (NonNegativeAbs evidence) otherSource y])
          checkSimplification otherSource (other { contextUsed = positiveContext }) `shouldBe` False
        _ -> fail "Expected nonnegativity evidence from the positive assumption"
    it "does not treat completion status as mathematical evidence" $ do
      let source = FracBinopE FDiv x x
      result <- expectRight (simplifyChecked 1 context source)
      checkSimplification source (result { completion = BudgetExhausted }) `shouldBe` True
  where
    context :: Context Double
    context = emptyContext realScalars

    x, y, zero, one :: Exp Double
    x = VarE "x"
    y = VarE "y"
    zero = ConstE (IntegerC 0)
    one = ConstE (IntegerC 1)

    candidate source target proof = do
      domain <- expectRight (domainOf context source)
      pure Simplification
        { contextUsed = context, original = source, value = target
        , sourceDomain = domain, obligations = trueCondition
        , derivation = proof, completion = NoApplicableRule
        }

    identities =
      [ (CancelDifference, NumBinopE Sub x x, zero)
      , (CancelQuotient, FracBinopE FDiv x x, one)
      , (CancelOpposites, NumBinopE Add x (NumUnopE Neg x), zero)
      , (ZeroProduct, NumBinopE Mul zero x, zero)
      , (CancelReciprocals, FracUnopE Recip (FracUnopE Recip x), x)
      , (PythagoreanIdentity, NumBinopE Add (NatPowE (FloatUnopE Sin x) 2)
                                           (NatPowE (FloatUnopE Cos x) 2), one)
      , (ZeroQuotient, FracBinopE FDiv zero x, zero)
      , (CancelProductNumerator, FracBinopE FDiv (NumBinopE Mul x y) x, y)
      , (CancelProductDenominator, FracBinopE FDiv x (NumBinopE Mul x y), FracUnopE Recip y)
      , (DivideIntegralPowers, FracBinopE FDiv (NatPowE x 5) (NatPowE x 2), IntPowE x 3)
      , (MultiplyIntegralPowers, NumBinopE Mul (NatPowE x 2) (IntPowE x (-1)), x)
      , (FlattenIntegralPowers, IntPowE (IntPowE x (-3)) (-2), NatPowE x 6)
      ]
