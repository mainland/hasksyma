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
import           Hasksyma.Const            (Const (..))
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
        result <- expectRight (simplifyChecked 1 context source)
        sameExp (value result) (ConstE (IntegerC 0)) `shouldBe` True
        expectNonZeroX (sourceDomain result)
        checkSimplification source result `shouldBe` True
    it "retains exclusions already established by the recorded context" $ do
      positiveContext <- expectRight (assuming (positive x) context)
      result <- expectRight (simplifyChecked 1 positiveContext (FracBinopE FDiv x x))
      expectNonZeroX (sourceDomain result)
      decision <- expectRight (decide (contextUsed result) (positive x))
      checkDecision (contextUsed result) (positive x) decision `shouldBe` True
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
      ]
