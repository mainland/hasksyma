{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  Test.Condition
-- Copyright   :  (c) 2026 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Condition (conditionTests) where

import           Control.Monad      (forM_)
import           Data.Complex       (Complex)
import           Data.List          (intercalate)
import           Data.Ratio         ((%))
import           Test.Hspec         (Spec, describe, it, shouldBe)

import           Hasksyma.Condition
import           Hasksyma.Const     (Const (..), IsConst (..))
import           Hasksyma.Exp

-- None of these methods is needed to reject an uninterpreted payload.
data Opaque = Opaque
    deriving Show

instance Eq Opaque where
    _ == _ = error "Condition checking compared an opaque payload"

instance IsConst Opaque where
    fromConst _ = error "Condition checking evaluated an opaque constant"
    exactRational _ = error "Condition checking projected an opaque payload"
    samePayload _ _ = error "Condition checking inspected an opaque payload"

data Verdict = Established | Disproved | Undetermined
    deriving (Eq, Show)

verdict :: Decision a -> Verdict
verdict Proved{}  = Established
verdict Refuted{} = Disproved
verdict Unknown   = Undetermined

expectRight :: Show e => Either e a -> IO a
expectRight = either (fail . show) pure

contextError :: Either ContextError a -> Maybe ContextError
contextError = either Just (const Nothing)

-- A client renderer uses only the public view and chooses how to render leaves.
renderCondition :: (Exp a -> String) -> Condition a -> String
renderCondition renderExpression condition = case viewCondition condition of
    TruthView True             -> "true"
    TruthView False            -> "false"
    DefinedView e              -> "defined(" ++ renderExpression e ++ ")"
    NonZeroView e              -> "nonzero(" ++ renderExpression e ++ ")"
    PositiveView e             -> "positive(" ++ renderExpression e ++ ")"
    NonNegativeView e          -> "nonnegative(" ++ renderExpression e ++ ")"
    ConjunctionView conditions ->
        "(" ++ intercalate " and " (map (renderCondition renderExpression) conditions) ++ ")"

conditionTests :: Spec
conditionTests = describe "Conditions" $ do
    describe "Structural inspection" $ do
      it "supports recursive rendering of normalized conditions and source domains" $ do
        let claim = allOf [defined x, allOf [nonZero x, trueCondition, positive y], nonNegative y]
            render = renderCondition (const "u")
        render claim `shouldBe` "(defined(u) and nonzero(u) and positive(u) and nonnegative(u))"
        render (allOf []) `shouldBe` "true"
        domain <- expectRight $ domainOf realContext (FracUnopE Recip (ConstE (IntegerC 0)))
        render domain `shouldBe` "false"
      it "allows rendering uninterpreted payloads without inspecting or validating them" $ do
        let claim = defined (ConstE (Const Opaque))
        renderCondition (const "opaque") claim `shouldBe` "defined(opaque)"
        (verdict <$> decide (emptyContext realScalars) claim) `shouldBe` Left UnsupportedConstant
    describe "Elementary real facts" $ do
      it "proves true and the empty conjunction without assumptions" $
        forM_ [trueCondition, allOf []] $ \claim -> do
          result <- expectRight $ decide realContext claim
          verdict result `shouldBe` Established
          checkDecision realContext claim result `shouldBe` True
          case result of
            Proved evidence -> length (assumptionsUsed evidence) `shouldBe` 0
            _               -> fail "Expected evidence for true"
      it "defines real variables without assuming their signs" $ do
        (verdict <$> decide realContext (defined x)) `shouldBe` Right Established
        forM_ [nonZero x, positive x, nonNegative x] $ \claim ->
          (verdict <$> decide realContext claim) `shouldBe` Right Undetermined
      it "proves the signs of positive exact constants" $
        forM_ [IntegerC 3, RationalC (1/3), Pi (1/7), E] $ \constant ->
          forM_ predicates $ \predicate ->
            (verdict <$> decide realContext (predicate (ConstE constant))) `shouldBe` Right Established
      it "refutes positivity and nonnegativity of negative exact constants" $
        forM_ [IntegerC (-3), RationalC (-1/3), Pi (-1/7)] $ \constant -> do
          let expression = ConstE constant
          forM_ [defined, nonZero] $ \predicate ->
            (verdict <$> decide realContext (predicate expression)) `shouldBe` Right Established
          forM_ [positive, nonNegative] $ \predicate ->
            (verdict <$> decide realContext (predicate expression)) `shouldBe` Right Disproved
      it "recognizes exact zero across its supported representations" $
        forM_ [IntegerC 0, RationalC 0, Pi 0] $ \constant -> do
          let expression = ConstE constant
          forM_ [defined, nonNegative] $ \predicate ->
            (verdict <$> decide realContext (predicate expression)) `shouldBe` Right Established
          forM_ [nonZero, positive] $ \predicate ->
            (verdict <$> decide realContext (predicate expression)) `shouldBe` Right Disproved
      it "determines huge and tiny exact signs without floating conversion" $ do
        let huge = 10^(400 :: Integer)
        forM_ [IntegerC huge, RationalC (1 % huge), Pi (fromInteger huge), Pi (1 % huge)] $ \constant ->
          (verdict <$> decide realContext (positive (ConstE constant))) `shouldBe` Right Established
        forM_ [IntegerC (-huge), RationalC ((-1) % huge), Pi (negate (fromInteger huge)), Pi ((-1) % huge)] $ \constant ->
          (verdict <$> decide realContext (nonNegative (ConstE constant))) `shouldBe` Right Disproved
      it "refutes every scalar predicate on exceptional leaves" $
        forM_ [Undefined, Infty, NegInfty] $ \expression ->
          forM_ predicates $ \predicate -> do
            let claim = predicate expression
            result <- expectRight $ decide realContext claim
            verdict result `shouldBe` Disproved
            checkDecision realContext claim result `shouldBe` True
      it "leaves arbitrary composite signs unknown without premises" $
        forM_ supportedExpressions $ \expression ->
          forM_ [nonZero, positive, nonNegative] $ \predicate ->
            (verdict <$> decide realContext (predicate expression)) `shouldBe` Right Undetermined
      it "does not infer definedness by erasing a zero power's base" $ do
        forM_ [NatPowE (FracUnopE Recip x) 0, IntPowE (FracUnopE Recip x) 0] $ \expression ->
          (verdict <$> decide realContext (defined expression)) `shouldBe` Right Undetermined
        (verdict <$> decide realContext (defined (IntPowE Undefined 0))) `shouldBe` Right Disproved
      it "proves a conjunction when every member is established" $ do
        let claim = allOf [defined x, positive (ConstE E), nonNegative (ConstE (IntegerC 0))]
        result <- expectRight $ decide realContext claim
        verdict result `shouldBe` Established
        checkDecision realContext claim result `shouldBe` True
      it "refutes a conjunction even when another member is unknown" $ do
        let unknown = positive x
            false = nonZero (ConstE (IntegerC 0))
        forM_ [[unknown, false], [false, unknown]] $ \claims -> do
          let claim = allOf claims
          result <- expectRight $ decide realContext claim
          verdict result `shouldBe` Disproved
          checkDecision realContext claim result `shouldBe` True
      it "does not confuse an unknown conjunction with a false one" $
        (verdict <$> decide realContext (allOf [defined x, positive x])) `shouldBe` Right Undetermined
    describe "Explicit assumptions" $ do
      it "accepts an unknown supported predicate as a hypothesis" $ do
        context <- expectRight $ assuming (nonZero x) realContext
        (verdict <$> decide context (nonZero x)) `shouldBe` Right Established
      it "derives nonzero, nonnegative, and defined from positive" $ do
        context <- expectRight $ assuming (positive x) realContext
        forM_ predicates $ \predicate ->
          (verdict <$> decide context (predicate x)) `shouldBe` Right Established
      it "does not strengthen a nonnegative premise to positive or nonzero" $ do
        context <- expectRight $ assuming (nonNegative x) realContext
        (verdict <$> decide context (defined x)) `shouldBe` Right Established
        forM_ [positive x, nonZero x] $ \claim ->
          (verdict <$> decide context claim) `shouldBe` Right Undetermined
      it "does not infer a sign from a nonzero premise" $ do
        context <- expectRight $ assuming (nonZero x) realContext
        (verdict <$> decide context (defined x)) `shouldBe` Right Established
        forM_ [positive x, nonNegative x] $ \claim ->
          (verdict <$> decide context claim) `shouldBe` Right Undetermined
      it "uses the members of a conjunctive assumption" $ do
        context <- expectRight $ assuming (allOf [positive x, nonZero y]) realContext
        forM_ [nonNegative x, nonZero x, defined y, nonZero y] $ \claim ->
          (verdict <$> decide context claim) `shouldBe` Right Established
      it "rejects hypotheses refuted by exact facts" $
        forM_ [nonZero (ConstE (IntegerC 0)), positive (ConstE (Pi (-1))), defined Undefined] $ \claim ->
          contextError (assuming claim realContext) `shouldBe` Just ContradictoryAssumptions
      it "rejects a false conjunction despite an unknown conjunct" $
        contextError (assuming (allOf [positive x, defined Infty]) realContext)
          `shouldBe` Just ContradictoryAssumptions
      it "keeps assumptions attached to their expressions" $ do
        context <- expectRight $ assuming (positive (NumBinopE Add x y)) realContext
        forM_ [positive x, positive y, positive (NumBinopE Mul x y)] $ \claim ->
          (verdict <$> decide context claim) `shouldBe` Right Undetermined
      it "allows explicit premises about supported composite expressions" $ do
        let expression = FracUnopE Recip x
        context <- expectRight $ assuming (positive expression) realContext
        result <- expectRight $ decide context (nonZero expression)
        verdict result `shouldBe` Established
        checkDecision context (nonZero expression) result `shouldBe` True
    describe "Interpretation boundaries" $ do
      it "rejects evaluated floating payloads including finite values" $
        forM_ [0, 1, 0/0, 1/0, -1/0] $ \payload ->
          (verdict <$> decide realContext (defined (ConstE (Const payload))))
            `shouldBe` Left UnsupportedConstant
      it "rejects an opaque payload without inspecting or evaluating it" $
        forM_ [Opaque, error "Forced opaque payload"] $ \payload -> do
          let claim = defined (ConstE (Const payload))
              context = emptyContext realScalars
          (verdict <$> decide context claim) `shouldBe` Left UnsupportedConstant
          contextError (assuming claim context) `shouldBe` Just UnsupportedConstant
      it "supports a complex carrier without an ordering constraint" $ do
        let variable = VarE "z" :: Exp (Complex Double)
            context :: Context (Complex Double)
            context = emptyContext realScalars
        (verdict <$> decide context (defined variable)) `shouldBe` Right Established
        (verdict <$> decide context (positive (ConstE E))) `shouldBe` Right Established
        assumed <- expectRight $ assuming (positive variable) context
        result <- expectRight $ decide assumed (nonZero variable)
        verdict result `shouldBe` Established
        checkDecision assumed (nonZero variable) result `shouldBe` True
      it "reports unaudited floating operations as unsupported" $
        forM_ unsupportedFloatingExpressions $ \expression ->
          (verdict <$> decide realContext (defined expression)) `shouldBe` Left UnsupportedOperation
      it "reports integral arithmetic as unsupported" $
        forM_ [Quot, Rem, Div, Mod] $ \operation ->
          (verdict <$> decide (emptyContext realScalars) (defined (IntBinopE operation (VarE "n") (ConstE (IntegerC 2)) :: Exp Integer)))
            `shouldBe` Left UnsupportedOperation
      it "does not cross derivative or integral binders" $
        forM_ [DiffE x "x", IntE Nothing x "x", IntE (Just (x, y)) x "x"] $ \expression ->
          (verdict <$> decide realContext (defined expression)) `shouldBe` Left UnsupportedOperation
      it "validates supported operations' children before reasoning" $ do
        let unsupported = FloatUnopE Log x
        forM_ [NumBinopE Add x unsupported, NumBinopE Mul (ConstE (IntegerC 0)) unsupported,
               NatPowE unsupported 0, IntPowE unsupported 0] $ \expression ->
          (verdict <$> decide realContext (defined expression)) `shouldBe` Left UnsupportedOperation
      it "validates every conjunct before deciding or assuming it" $ do
        let unsupported = defined (FloatUnopE Log x)
            false = defined Undefined
        forM_ [[false, unsupported], [unsupported, false], [trueCondition, unsupported]] $ \claims -> do
          (verdict <$> decide realContext (allOf claims)) `shouldBe` Left UnsupportedOperation
          contextError (assuming (allOf claims) realContext) `shouldBe` Just UnsupportedOperation
#if defined(CYCLOTOMIC)
      it "reports real cyclotomic constants as unsupported" $
        (verdict <$> decide realContext (defined (ConstE (RealCycC 1)))) `shouldBe` Left UnsupportedConstant
      it "reports complex cyclotomic constants as unsupported" $
        (verdict <$> decide (emptyContext realScalars) (defined (ConstE (CycC 1) :: Exp (Complex Double))))
          `shouldBe` Left UnsupportedConstant
#endif
    describe "Exact source domains" $ do
      it "recognizes total real arithmetic and trigonometric expressions" $
        forM_ [NumBinopE Sub x x, NumUnopE Abs x, NumUnopE Signum x,
               NatPowE x 0, IntPowE x 3, FloatUnopE Sin x, FloatUnopE Cos x] $ \expression -> do
          checkDomain realContext expression trueCondition `shouldBe` True
          result <- expectRight $ decide realContext (defined expression)
          verdict result `shouldBe` Established
          checkDecision realContext (defined expression) result `shouldBe` True
      it "retains reciprocal singularities in cancelled or erased operands" $ do
        let inverse = FracUnopE Recip x
        forM_ [inverse, NumBinopE Sub inverse inverse,
               NumBinopE Mul (ConstE (IntegerC 0)) inverse,
               NatPowE inverse 0, IntPowE inverse 0,
               FloatUnopE Sin inverse] $ \expression -> do
          checkDomain realContext expression (nonZero x) `shouldBe` True
          checkDomain realContext expression trueCondition `shouldBe` False
      it "retains both numerator and denominator restrictions" $ do
        let expression = FracBinopE FDiv (FracUnopE Recip x) y
        checkDomain realContext expression (allOf [nonZero x, nonZero y]) `shouldBe` True
        checkDomain realContext expression (nonZero y) `shouldBe` False
      it "preserves nested reciprocal requirements without minimizing them" $ do
        let inverse = FracUnopE Recip x
            expression = FracUnopE Recip inverse
        checkDomain realContext expression (allOf [nonZero x, nonZero inverse]) `shouldBe` True
      it "requires a nonzero base for negative integral powers" $ do
        checkDomain realContext (IntPowE x (-3)) (nonZero x) `shouldBe` True
        checkDomain realContext (NatPowE x 3) trueCondition `shouldBe` True
      it "does not replace an exact domain with a sufficient positivity condition" $
        checkDomain realContext (FracUnopE Recip x) (positive x) `shouldBe` False
      it "retains exclusions even when the context establishes them" $ do
        context <- expectRight $ assuming (positive x) realContext
        let expression = FracUnopE Recip x
        domain <- expectRight $ domainOf context expression
        checkDomain realContext expression domain `shouldBe` True
        checkDomain context expression trueCondition `shouldBe` False
        (verdict <$> decide context domain) `shouldBe` Right Established
      it "recognizes closed reciprocal and power domains exactly" $
        forM_ [-2, 0, 3] $ \base ->
          forM_ [-3, 0, 2] $ \power -> do
            let expression = IntPowE (ConstE (IntegerC base)) power
                expected = if power < 0 && base == 0 then Disproved else Established
            domain <- expectRight $ domainOf realContext expression
            (verdict <$> decide realContext domain) `shouldBe` Right expected
            (verdict <$> decide realContext (defined expression)) `shouldBe` Right expected
      it "propagates empty domains through strict operations" $ do
        let failure = FracBinopE FDiv (ConstE (IntegerC 1)) (ConstE (IntegerC 0))
        forM_ [failure, FracUnopE Recip failure,
               NumBinopE Mul (ConstE (IntegerC 0)) failure,
               NatPowE failure 0, IntPowE failure 0,
               NumUnopE Abs failure, FloatUnopE Cos failure] $ \expression -> do
          domain <- expectRight $ domainOf realContext expression
          (verdict <$> decide realContext domain) `shouldBe` Right Disproved
          forM_ predicates $ \predicate -> do
            let claim = predicate expression
            result <- expectRight $ decide realContext claim
            verdict result `shouldBe` Disproved
            checkDecision realContext claim result `shouldBe` True
      it "rejects assumptions about expressions known to have no value" $
        forM_ predicates $ \predicate ->
          contextError (assuming (predicate (FracUnopE Recip (ConstE (IntegerC 0)))) realContext)
            `shouldBe` Just ContradictoryAssumptions
      it "validates all syntax before absorbing a false domain" $ do
        let unsupported = FloatUnopE Log x
        forM_ [NumBinopE Mul Undefined unsupported,
               NumBinopE Add unsupported Undefined,
               NatPowE unsupported 0] $ \expression -> do
          contextError (domainOf realContext expression) `shouldBe` Just UnsupportedOperation
          checkDomain realContext expression trueCondition `shouldBe` False
      it "rejects unsupported proposed domain conditions" $
        checkDomain realContext x (defined (ConstE (Const (1 :: Double)))) `shouldBe` False
      it "replays definedness evidence using the required hypotheses" $ do
        left <- expectRight $ assuming (positive x) realContext
        right <- expectRight $ assuming (nonZero y) realContext
        both <- expectRight $ assuming (nonZero y) left
        let claim = defined (NumBinopE Add (FracUnopE Recip x) (IntPowE y (-2)))
        result <- expectRight $ decide both claim
        verdict result `shouldBe` Established
        checkDecision both claim result `shouldBe` True
        checkDecision left claim result `shouldBe` False
        checkDecision right claim result `shouldBe` False
        case result of
          Proved evidence -> length (assumptionsUsed evidence) `shouldBe` 2
          _               -> fail "Expected evidence for the source domain"
      it "rejects domain evidence for another expression or polarity" $ do
        context <- expectRight $ assuming (nonZero x) realContext
        let claim = defined (FracUnopE Recip x)
        result <- expectRight $ decide context claim
        checkDecision context (defined (FracUnopE Recip y)) result `shouldBe` False
        case result of
          Proved evidence -> checkDecision context claim (Refuted evidence) `shouldBe` False
          _               -> fail "Expected definedness evidence"
      it "terminates through nested negative and zero powers" $ do
        let expression = iterate (\e -> NatPowE (IntPowE e (-1)) 0) x !! 10
        (verdict <$> decide realContext (defined expression)) `shouldBe` Right Undetermined
      it "does not require an ordered numerical carrier" $ do
        let expression = FracUnopE Recip (VarE "z") :: Exp (Complex Double)
        domain <- expectRight $ domainOf (emptyContext realScalars) expression
        checkDomain (emptyContext realScalars) expression domain `shouldBe` True
    describe "Evidence replay" $ do
      it "replays every premise used by a conjunction" $ do
        left <- expectRight $ assuming (positive x) realContext
        right <- expectRight $ assuming (positive y) realContext
        both <- expectRight $ assuming (positive y) left
        let claim = allOf [nonZero x, nonNegative y]
        result <- expectRight $ decide both claim
        verdict result `shouldBe` Established
        checkDecision both claim result `shouldBe` True
        checkDecision left claim result `shouldBe` False
        checkDecision right claim result `shouldBe` False
        case result of
          Proved evidence -> length (assumptionsUsed evidence) `shouldBe` 2
          _               -> fail "Expected evidence using both premises"
      it "replays with the original and strengthened contexts but rejects missing premises" $ do
        context <- expectRight $ assuming (positive x) realContext
        stronger <- expectRight $ assuming (nonZero y) context
        let claim = nonZero x
        result <- expectRight $ decide context claim
        checkDecision context claim result `shouldBe` True
        checkDecision stronger claim result `shouldBe` True
        checkDecision realContext claim result `shouldBe` False
        case result of
          Proved evidence -> length (assumptionsUsed evidence) `shouldBe` 1
          _               -> fail "Expected evidence using the positive premise"
      it "does not retain unrelated context assumptions as proof dependencies" $ do
        context <- expectRight $ assuming (positive x) realContext
        stronger <- expectRight $ assuming (nonZero y) context
        result <- expectRight $ decide stronger (nonZero x)
        checkDecision context (nonZero x) result `shouldBe` True
      it "rejects evidence for a different claim even when that claim is true" $ do
        result <- expectRight $ decide realContext (defined x)
        checkDecision realContext (defined y) result `shouldBe` False
        checkDecision realContext (positive x) result `shouldBe` False
      it "rejects proof evidence presented as a refutation" $ do
        result <- expectRight $ decide realContext (defined x)
        case result of
          Proved evidence -> checkDecision realContext (defined x) (Refuted evidence) `shouldBe` False
          _               -> fail "Expected a proof of variable definedness"
      it "rejects refutation evidence presented as a proof" $ do
        let claim = positive (ConstE (IntegerC (-1)))
        result <- expectRight $ decide realContext claim
        case result of
          Refuted evidence -> checkDecision realContext claim (Proved evidence) `shouldBe` False
          _                -> fail "Expected a refutation of negative positivity"
      it "does not accept unknown as checked evidence" $
        checkDecision realContext (positive x) Unknown `shouldBe` False
  where
    realContext :: Context Double
    realContext = emptyContext realScalars

    x, y :: Exp Double
    x = VarE "x"
    y = VarE "y"

    predicates :: [Exp Double -> Condition Double]
    predicates = [defined, nonZero, positive, nonNegative]

    supportedExpressions :: [Exp Double]
    supportedExpressions =
        [ NumUnopE operation x | operation <- [Neg, Abs, Signum] ] ++
        [ NumBinopE operation x y | operation <- [Add, Sub, Mul] ] ++
        [ FracUnopE Recip x
        , FracBinopE FDiv x y
        , NatPowE x 2
        , IntPowE x (-2)
        , FloatUnopE Sin x
        , FloatUnopE Cos x
        ]

    unsupportedFloatingExpressions :: [Exp Double]
    unsupportedFloatingExpressions =
        [ FloatUnopE operation x | operation <- [Exp, Log, Sqrt, Tan, Asin, Acos, Atan,
                                                 Sinh, Cosh, Tanh, Asinh, Acosh, Atanh] ] ++
        [ FracPowE x (1/2)
        , FloatBinopE Pow x y
        , FloatBinopE Root x y
        , FloatBinopE LogBase x y
        ]
