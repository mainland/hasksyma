{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  Test.Simplify
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Simplify where

import           Control.Exception               (evaluate)
import           Control.Monad                   (forM_)
import           Data.Complex                    (Complex (..), magnitude)
import           System.Timeout                  (timeout)
import           Test.Hspec
import           Test.HUnit
import           Test.QuickCheck
import           Text.PrettyPrint.Mainland       (prettyCompact, text, (<+>))
import           Text.PrettyPrint.Mainland.Class (ppr)

import           Hasksyma.Const
import           Hasksyma.Eval
import           Hasksyma.Exp
import           Hasksyma.Simplify

import           Test.Eval

simplifyTests :: Spec
simplifyTests = describe "Simplification" $ do
    describe "Numeric test helpers" $ do
      forM_ [("zeros", 0, 0), ("equal values", 2, 2),
             ("nearby values", 1, 1 + 1e-13)] $ \(name, x, y) ->
        it ("accepts " ++ name) $
          equiv eps (ConstE (Const x)) (ConstE (Const y))
      it "rejects unequal finite values" $
        expectFailure $ equiv eps 1 2
      forM_ [("NaN", 0/0), ("positive infinity", 1/0), ("negative infinity", -1/0)] $ \(name, x) ->
        forM_ [("left", x, 1), ("right", 1, x), ("both", x, x)] $ \(position, a, b) ->
          it ("rejects " ++ name ++ " in " ++ position ++ " operands") $
            expectFailure $ equiv eps (ConstE (Const a)) (ConstE (Const b))
      forM_ [Undefined, Infty, NegInfty, VarE "x"] $ \e ->
        it ("rejects unevaluated operands: " ++ show e) $
          expectFailure $ equiv eps e e
      forM_ [("zero", 0), ("negative", -1), ("NaN", 0/0), ("infinite", 1/0)] $ \(name, tolerance) ->
        it ("rejects " ++ name ++ " tolerance") $
          expectFailure $ equiv tolerance 0 0
    identityTests
    terminationTests
    mapExpTests
    integerLogTests
    logDomainTests
    logInverseTests
    generalPowerDomainTests
    zeroPowerTests
    zeroDivisionTests
    exactNegationTests
    fixExpTests
    norvigTests
    prodTests
    powTests
    it "Simplification preserves exactness and evaluation" $
        property $ forAllShrinkBlind arbitrary shrink $ popEvalSimplifyEquiv eps tensec
  where
    eps :: Double
    eps = 1e-12

    tensec :: Int
    tensec = 10 * 1000000

exactNegationTests :: Spec
exactNegationTests = describe "Exact negation" $ do
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) -> do
      forM_ expressions $ \(form, e) ->
        it (name ++ " preserves exactness in " ++ form) $ do
          isExactE (transform e) @?= True
          value (transform e) @?= value e
      it (name ++ " agrees with exact evaluation of negative Euler's number") $
        sameExp (transform negativeE) (evalexact negativeE) @?= True
      it (name ++ " still folds negation of exact numeric constants") $
        forM_ [IntegerC (10^(100 :: Integer)), RationalC (3/2), Pi 1, Pi (-1)] $ \c -> do
          let result = transform (NumUnopE Neg (ConstE c) :: Exp Double)
          isExactE result @?= True
          result @?= ConstE (-c)
      it (name ++ " leaves evaluated payloads for numerical evaluation") $
        forM_ [2, 0/0, 1/0, -1/0] $ \payload -> do
          let e = NumUnopE Neg (ConstE (Const payload)) :: Exp Double
          sameExp (transform e) e @?= True
          samePayload (value (transform e)) (-payload) @?= True
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) ->
      it (name ++ " preserves negative Euler's number with complex payloads") $
        let e = NumUnopE Neg (ConstE E) :: Exp (Complex Double)
        in sameExp (transform e) e @?= True
  where
    negativeE :: Exp Double
    negativeE = NumUnopE Neg (ConstE E)

    expressions :: [(String, Exp Double)]
    expressions =
      [ ("negative Euler's number", negativeE)
      , ("double negation", NumUnopE Neg negativeE)
      , ("a sum containing negative Euler's number", NumBinopE Add 1 negativeE)
      , ("a product containing negative Euler's number", NumBinopE Mul (VarE "x") negativeE)
      ]

    value :: Exp Double -> Double
    value e = case eval (mapExp replace e) of
                ConstE c -> fromConst c
                result   -> error (show result)
      where
        replace VarE{} = 2
        replace other  = other

identityTests :: Spec
identityTests = describe "Expression identity" $ do
    it "recognizes unchanged NaN syntax without changing equality" $ do
      let e = FloatUnopE Sin (ConstE (Const (0/0))) :: Exp Double
      sameExp e e @?= True
      (e == e) @?= False
    it "distinguishes equal constant representations inside expressions" $ do
      let a = NumUnopE Neg (ConstE (IntegerC 1)) :: Exp Double
          b = NumUnopE Neg (ConstE (RationalC 1))
      (a == b) @?= True
      sameExp a b @?= False
    it "compares operator and power syntax independently of numeric equality" $ do
      let x = VarE "x" :: Exp Double
      sameExp (NumUnopE Neg x) (NumUnopE Abs x) @?= False
      sameExp (NatPowE x 2) (IntPowE x 2) @?= False
      sameExp (FracPowE x (1/2)) (FracPowE x (1/3)) @?= False
    it "checks calculus variables and both integral bounds around NaNs" $ do
      let nan = ConstE (Const (0/0)) :: Exp Double
          integral l u = IntE (Just (l, u)) nan
      sameExp (integral nan 1 "x") (integral nan 1 "x") @?= True
      sameExp (integral nan 1 "x") (integral nan 2 "x") @?= False
      sameExp (integral 0 nan "x") (integral 1 nan "x") @?= False
      sameExp (integral nan 1 "x") (integral nan 1 "y") @?= False
      sameExp (integral nan 1 "x") (IntE Nothing nan "x") @?= False
      sameExp (IntE Nothing nan "x") (IntE Nothing nan "x") @?= True
      sameExp (IntE Nothing nan "x") (IntE Nothing 1 "x") @?= False
      sameExp (DiffE nan "x") (DiffE nan "y") @?= False

zeroDivisionTests :: Spec
zeroDivisionTests = describe "Division by known zero" $ do
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify'), ("evalexact", evalexact)] $
      \(name, transform) ->
        it (name ++ " preserves the division for every numerator and zero representation") $
          forM_ [0, 1, ConstE (IntegerC (-1)), VarE "x", Undefined, Infty, NegInfty] $ \numerator ->
            forM_ [IntegerC 0, RationalC 0, Pi 0, Const 0, Const (-0.0)] $ \denominator ->
              let e = FracBinopE FDiv numerator (ConstE denominator) :: Exp Double
              in sameExp (transform e) e @?= True
    it "preserves division by a denominator that simplifies to zero" $
      let e = FracBinopE FDiv (-1) (NumBinopE Sub 2 2) :: Exp Double
      in sameExp (simplify e) (FracBinopE FDiv (ConstE (IntegerC (-1))) 0) @?= True
    it "preserves division by zero with exact rational payloads" $
      forM_ [0, 1, ConstE (IntegerC (-1))] $ \numerator ->
        let e = FracBinopE FDiv numerator 0 :: Exp Rational
        in sameExp (simplify e) e @?= True
    it "preserves division by zero with complex payloads" $
      forM_ [0, 1, ConstE (IntegerC (-1)), ConstE (Const (0 :+ 1))] $ \numerator ->
        let e = FracBinopE FDiv numerator 0 :: Exp (Complex Double)
        in sameExp (simplify e) e @?= True
    it "still reduces exact division by a nonzero denominator" $
      simplify (FracBinopE FDiv (-3) 2 :: Exp Rational) @?= ConstE (RationalC (-3/2))

zeroPowerTests :: Spec
zeroPowerTests = describe "Integral zero powers" $ do
    forM_ [("natural", (`NatPowE` 0)), ("signed", (`IntPowE` 0))] $ \(name, power) ->
      forM_ [("eval", eval), ("evalexact", evalexact), ("simplify", simplify), ("simplify'", simplify')] $
        \(operation, transform) ->
          it (operation ++ " returns exact one for " ++ name ++ " zero to the zero power") $
            forM_ [IntegerC 0, RationalC 0, Const 0, Const (-0.0)] $ \c ->
              sameExp (transform (power (ConstE c)) :: Exp Double) (ConstE (IntegerC 1)) @?= True
    it "uses the same convention with exact rational payloads" $
      forM_ [NatPowE 0 0, IntPowE 0 0] $ \e -> do
        sameExp (eval e :: Exp Rational) (ConstE (IntegerC 1)) @?= True
        sameExp (evalexact e) (ConstE (IntegerC 1)) @?= True
        sameExp (simplify e) (ConstE (IntegerC 1)) @?= True
    it "uses the same integral-power convention with complex payloads" $
      forM_ [NatPowE 0 0, IntPowE 0 0] $ \e -> do
        sameExp (eval e :: Exp (Complex Double)) (ConstE (IntegerC 1)) @?= True
        sameExp (evalexact e) (ConstE (IntegerC 1)) @?= True
        sameExp (simplify e) (ConstE (IntegerC 1)) @?= True
    it "still leaves a negative power of exact zero unreduced during exact evaluation" $
      let e = IntPowE 0 (-1) :: Exp Rational
      in sameExp (evalexact e) e @?= True

generalPowerDomainTests :: Spec
generalPowerDomainTests = describe "General power domains" $ do
    forM_ [("product", NumBinopE Mul p q),
           ("quotient", FracBinopE FDiv p q),
           ("natural outer power", NatPowE p 2),
           ("negative outer power", IntPowE p (-2))] $ \(name, e) ->
      it ("preserves an unknown base in a " ++ name) $
        sameExp (simplify e) e @?= True
    forM_ [("product", NumBinopE Mul a b),
           ("identical factors", NumBinopE Mul a a),
           ("product with a coefficient", NumBinopE Mul (NumBinopE Mul 3 a) b),
           ("quotient", FracBinopE FDiv a b),
           ("natural outer power", NatPowE a 2),
           ("negative outer power", IntPowE a (-2))] $ \(name, e) ->
      it ("preserves the negative real domain in a " ++ name) $
        case (eval e, eval (simplify e)) of
          (ConstE original, ConstE simplified) -> do
            assertBool "The original power is outside the real domain" (isNaN (fromConst original))
            assertBool "Simplification must preserve the domain failure" (isNaN (fromConst simplified))
          result -> assertFailure $ show result
    it "still combines general powers of an explicit positive exact base" $ do
      simplify (NumBinopE Mul u v) @?= FloatBinopE Pow 2 (y + z)
      simplify (FracBinopE FDiv u v) @?= FloatBinopE Pow 2 (y - z)
    it "still flattens integer powers of a general power with a positive exact base" $ do
      simplify (NatPowE u 2) @?= FloatBinopE Pow 2 (2*y)
      simplify (IntPowE u (-2)) @?= FloatBinopE Pow 2 (ConstE (IntegerC (-2))*y)
  where
    x, y, z :: Exp Double
    x = VarE "x"
    y = VarE "y"
    z = VarE "z"
    p = FloatBinopE Pow x y
    q = FloatBinopE Pow x z
    u = FloatBinopE Pow 2 y
    v = FloatBinopE Pow 2 z
    a = FloatBinopE Pow (ConstE (Const (-1))) (ConstE (Const (1/2))) :: Exp Double
    b = FloatBinopE Pow (ConstE (Const (-1))) (ConstE (Const (3/2))) :: Exp Double

logInverseTests :: Spec
logInverseTests = describe "Logarithm inverse conditions" $ do
    it "keeps exp and log when the argument domain is unknown" $
      sameExp (simplify (FloatUnopE Exp (FloatUnopE Log x)))
              (FloatBinopE Pow (ConstE E) (FloatUnopE Log x)) @?= True
    it "keeps log and exp when the exponent branch is unknown" $
      sameExp (simplify (FloatUnopE Log (FloatUnopE Exp x)))
              (FloatUnopE Log (FloatBinopE Pow (ConstE E) x)) @?= True
    it "preserves the real domain failure in exp (log (-2))" $
      case eval (simplify (FloatUnopE Exp (FloatUnopE Log (-2))) :: Exp Double) of
        ConstE c -> assertBool "Expected NaN" (isNaN (fromConst c))
        result   -> assertFailure $ show result
    it "preserves the principal branch in log (exp (4*i))" $
      let e = FloatUnopE Log (FloatUnopE Exp (ConstE (Const (0 :+ 4)))) :: Exp (Complex Double)
      in case (eval e, eval (simplify e)) of
        (ConstE original, ConstE simplified) ->
          assertBool "Expected the principal logarithm value"
                     (magnitude (fromConst original - fromConst simplified) < 1e-12)
        result -> assertFailure $ show result
    it "preserves the principal branch in logBase of a complex power" $
      let e = FloatBinopE LogBase 2 (FloatBinopE Pow 2 (ConstE (Const (0 :+ 6)))) :: Exp (Complex Double)
      in case (eval e, eval (simplify e)) of
        (ConstE original, ConstE simplified) ->
          assertBool "Expected the principal logarithm value"
                     (magnitude (fromConst original - fromConst simplified) < 1e-12)
        result -> assertFailure $ show result
    it "keeps logBase of a power when the base domain is unknown" $
      let e = FloatBinopE LogBase x (NatPowE x 2)
      in sameExp (simplify e) e @?= True
    it "keeps logBase of a power when the exponent branch is unknown" $
      let e = FloatBinopE LogBase 2 (FloatBinopE Pow 2 x)
      in sameExp (simplify e) e @?= True
    it "keeps logBase of one when the base domain is unknown" $
      let e = FloatBinopE LogBase x 1
      in sameExp (simplify e) e @?= True
    forM_ [("unit base", FloatBinopE LogBase 1 1),
           ("negative base", FloatBinopE LogBase (-2) (NatPowE (-2) 2))] $ \(name, e) ->
      it ("preserves the real domain failure for a " ++ name) $
        case eval (simplify e :: Exp Double) of
          ConstE c -> assertBool "Expected NaN" (isNaN (fromConst c))
          result   -> assertFailure $ show result
    it "still cancels exp and log for a positive exact argument" $
      forM_ [IntegerC 2, RationalC (3/2), Pi 1, E] $ \c ->
        simplify (FloatUnopE Exp (FloatUnopE Log (ConstE c)) :: Exp Double) @?= ConstE c
    it "still cancels log and powers for exact rational exponents" $
      forM_ [(NatPowE (ConstE E) 2, 2),
             (IntPowE (ConstE E) (-2), ConstE (IntegerC (-2))),
             (FracPowE (ConstE E) (1/2), ConstE (RationalC (1/2)))] $ \(e, expected) ->
        simplify (FloatUnopE Log e :: Exp Double) @?= expected
    it "still cancels logBase for positive exact bases and rational exponents" $ do
      simplify (FloatBinopE LogBase 2 (FracPowE 2 (1/2)) :: Exp Double) @?= ConstE (RationalC (1/2))
      simplify (FloatBinopE LogBase 2 1 :: Exp Double) @?= 0
  where
    x = VarE "x" :: Exp Double

logDomainTests :: Spec
logDomainTests = describe "Logarithm domains and branches" $ do
    forM_ realLogs $ \(name, logarithm) ->
      forM_ [Add, Sub] $ \op -> do
        it (name ++ " preserves unknown arguments under " ++ show op) $
          let e = NumBinopE op (logarithm (VarE "x")) (logarithm (VarE "y"))
          in sameExp (simplify e) e @?= True
        it (name ++ " preserves the real domain under " ++ show op) $
          let e = NumBinopE op (logarithm (ConstE (Const (-1))))
                              (logarithm (ConstE (Const (-2))))
          in case (eval e, eval (simplify e)) of
            (ConstE original, ConstE simplified) -> do
              assertBool "Original logarithms are outside the real domain" (isNaN (fromConst original))
              assertBool "Simplification must preserve the domain failure" (isNaN (fromConst simplified))
            result -> assertFailure $ show result
    forM_ complexLogs $ \(name, logarithm) ->
      forM_ [Add, Sub] $ \op ->
        it (name ++ " preserves the complex branch under " ++ show op) $
          let z = ConstE (Const ((-1) :+ 1))
              w = ConstE (Const ((-2) :+ (if op == Add then 1 else -1)))
              e = NumBinopE op (logarithm z) (logarithm w)
          in case (eval e, eval (simplify e)) of
            (ConstE original, ConstE simplified) ->
              assertBool "Simplification must preserve the principal logarithm value"
                         (magnitude (fromConst original - fromConst simplified) < 1e-12)
            result -> assertFailure $ show result
  where
    realLogs :: [(String, Exp Double -> Exp Double)]
    realLogs = [("log", FloatUnopE Log), ("logBase", FloatBinopE LogBase 2)]

    complexLogs :: [(String, Exp (Complex Double) -> Exp (Complex Double))]
    complexLogs = [("log", FloatUnopE Log), ("logBase", FloatBinopE LogBase 2)]

integerLogTests :: Spec
integerLogTests = describe "Exact integer logarithm recognition" $ do
    forM_ [(1, 1), (-2, 4), (0, 0), (2, 0), (2, -1)] $ \(b, y) ->
      it ("leaves invalid logBase " ++ show b ++ " " ++ show y ++ " unreduced") $
        let e = logarithm b y
        in assertTerminates $ sameExp (evalexact e) e
    it "leaves an infinite logarithm estimate unreduced" $
      let e = logarithm 2 huge
      in assertTerminates $ sameExp (evalexact e) e
    it "leaves a NaN logarithm estimate unreduced" $
      let e = logarithm huge huge
      in assertTerminates $ sameExp (evalexact e) e
    it "still recognizes exact nonnegative integer logarithms" $
      forM_ [(2, 1, 0), (2, 8, 3), (10, 1000, 3), (3, 3 ^ (30 :: Integer), 30)] $ \(b, y, n) ->
        sameExp (evalexact (logarithm b y)) (ConstE (IntegerC n)) @?= True
    it "does not fold a rounded estimate unless exact exponentiation agrees" $
      forM_ [(2, 3), (3, 10), (2, 2 ^ (53 :: Integer) + 1)] $ \(b, y) ->
        let e = logarithm b y
        in sameExp (evalexact e) e @?= True
  where
    logarithm :: Integer -> Integer -> Exp Double
    logarithm b y = FloatBinopE LogBase (ConstE (IntegerC b)) (ConstE (IntegerC y))

    huge = 2 ^ (2048 :: Integer)

mapExpTests :: Spec
mapExpTests = describe "Expression traversal" $ do
    forM_ [("undefined", Undefined), ("positive infinity", Infty),
           ("negative infinity", NegInfty), ("constant", ConstE (IntegerC 1)),
           ("variable", VarE "x")] $ \(name, leaf) ->
      it ("applies the callback to a " ++ name ++ " leaf") $
        sameExp (mapExp (const done) leaf) done @?= True
    forM_ contexts $ \(name, wrap) ->
      it ("transforms leaves inside " ++ name) $
        sameExp (mapExp rename (wrap (VarE "x"))) (wrap (VarE "y")) @?= True
    it "transforms leaves inside integral binary operations" $
      let e = IntBinopE Quot (VarE "x") (VarE "x") :: Exp Integer
      in sameExp (mapExp rename e) (IntBinopE Quot (VarE "y") (VarE "y")) @?= True
    it "passes transformed children to the parent callback" $
      let step VarE{}                                                      = ConstE (IntegerC 1)
          step (NumBinopE Add (ConstE (IntegerC 1)) (ConstE (IntegerC 1))) = done
          step e                                                           = e
      in sameExp (mapExp step (NumBinopE Add (VarE "x") (VarE "x"))) done @?= True
    it "does not revisit nodes introduced by the callback" $
      assertTerminates $
        sameExp (mapExp (NumUnopE Neg) (NumUnopE Abs (VarE "x") :: Exp Double))
                (NumUnopE Neg (NumUnopE Abs (NumUnopE Neg (VarE "x"))))
    it "does not force a constant payload that the callback discards" $
      sameExp (mapExp (const done) (ConstE (Const (error "Unused payload")))) done @?= True
  where
    done :: Exp Double
    done = VarE "done"

    rename :: Exp a -> Exp a
    rename (VarE "x") = VarE "y"
    rename e          = e

    contexts :: [(String, Exp Double -> Exp Double)]
    contexts = [("numeric unary operations", NumUnopE Abs),
                ("fractional unary operations", FracUnopE Recip),
                ("floating unary operations", FloatUnopE Sin),
                ("numeric binary operations", \e -> NumBinopE Add e e),
                ("natural powers", (`NatPowE` 2)),
                ("integer powers", (`IntPowE` (-2))),
                ("fractional powers", (`FracPowE` (1/2))),
                ("fractional binary operations", \e -> FracBinopE FDiv e e),
                ("floating binary operations", \e -> FloatBinopE Pow e e),
                ("derivatives without renaming their variable field", (`DiffE` "x")),
                ("indefinite integrals without renaming their variable field", \e -> IntE Nothing e "x"),
                ("definite integral bounds and integrand without renaming the bound variable", \e -> IntE (Just (e, e)) e "x")]

fixExpTests :: Spec
fixExpTests = describe "Local fixed-point traversal" $ do
    it "returns leaves without invoking the rewrite or comparing payloads" $
      assertTerminates $ case fixExp (error "The rewrite must not be called") (ConstE (Const Opaque)) of
        ConstE (Const Opaque) -> True
        _                     -> False
    it "finishes rewriting a child before rewriting its parent" $
      sameExp (fixExp step (NumUnopE Abs (NatPowE x 3))) (VarE "done") @?= True
    it "rewrites children introduced by a parent rewrite" $
      sameExp (fixExp step (NumUnopE Neg x)) (VarE "done") @?= True
    it "rewrites both integral bounds and the integrand to fixed points" $
      sameExp (fixExp step (IntE (Just (NatPowE x 3, NatPowE x 2)) (NatPowE x 1) "t"))
              (IntE (Just (x, x)) x "t") @?= True
  where
    x = VarE "x" :: Exp Double

    step (NatPowE e n) | n > 1 = NatPowE e (fromInteger (toInteger n-1))
    step (NatPowE e _)         = e
    step (NumUnopE Neg e)      = NumUnopE Abs (NatPowE e 3)
    step (NumUnopE Abs VarE{}) = VarE "done"
    step (NumUnopE Abs _)      = VarE "early"
    step e                    = e

terminationTests :: Spec
terminationTests = describe "Rewrite termination" $ do
    forM_ [("simplify", simplify), ("simplify'", simplify')] $ \(name, simplifyWith) ->
      describe name $ do
        it "terminates on a constant NaN" $
          assertTerminates $ case simplifyWith (ConstE (Const (0/0)) :: Exp Double) of
            ConstE (Const value) -> isNaN value
            _                    -> False
        it "terminates with NaN inside an unchanged expression" $
          assertTerminates $ case simplifyWith (FloatUnopE Sin (ConstE (Const (0/0))) :: Exp Double) of
            FloatUnopE Sin (ConstE (Const value)) -> isNaN value
            _                                     -> False
        it "still simplifies siblings beside a NaN" $
          let e = NumBinopE Add (ConstE (Const (0/0))) (NumBinopE Add (VarE "x") 0)
          in assertTerminates $ case simplifyWith e of
            NumBinopE Add (VarE _) (ConstE (Const value)) -> isNaN (value :: Double)
            _                                             -> False
    it "terminates for complex NaN payloads" $
      assertTerminates $ case simplify (FloatUnopE Sin (ConstE (Const ((0/0) :+ 2))) :: Exp (Complex Double)) of
        FloatUnopE Sin (ConstE (Const (r :+ i))) -> isNaN r && i == 2
        _                                        -> False
    it "terminates when fixExp is given an identity rewrite around NaN" $
      assertTerminates $ case fixExp id (NumUnopE Neg (ConstE (Const (0/0))) :: Exp Double) of
        NumUnopE Neg (ConstE (Const value)) -> isNaN value
        _                                   -> False
    it "treats a negative simplifyn budget as zero work" $
      assertTerminates $ case simplifyn (-1) (ConstE (Const (0/0)) :: Exp Double) of
        ConstE (Const value) -> isNaN value
        _                    -> False
    it "does not use NaN syntax identity for algebraic cancellation" $
      let nan = ConstE (Const (0/0)) :: Exp Double
      in assertTerminates $ case simplify (NumBinopE Sub nan nan) of
        NumBinopE Sub (ConstE (Const a)) (ConstE (Const b)) -> isNaN a && isNaN b
        _                                                   -> False

    describe "Bounded rewriting" $ do
      it "reports an unchanged NaN as a fixed point" $
        assertTerminates $ case simplifyWithLimit 1 (ConstE (Const (0/0)) :: Exp Double) of
          FixedPoint (ConstE (Const value)) -> isNaN value
          _                                 -> False
      it "does no work for nonpositive budgets" $
        forM_ [0, -1, minBound] $ \limit ->
          case rewriteWithLimit limit (error "The rewrite must not be called") (VarE "x" :: Exp Double) of
            StepLimitReached e -> sameExp e (VarE "x") @?= True
            result             -> assertFailure $ show result
      it "distinguishes an exhausted simplification budget from completion" $ do
        let e = NumBinopE Add (VarE "x") 0 :: Exp Double
        case simplifyWithLimit 1 e of
          StepLimitReached result -> sameExp result (VarE "x") @?= True
          result                  -> assertFailure $ show result
        case simplifyWithLimit 2 e of
          FixedPoint result -> sameExp result (VarE "x") @?= True
          result            -> assertFailure $ show result
      it "retains a representation-changing step between equal constants" $ do
        let step (ConstE IntegerC{}) = ConstE (RationalC 1)
            step e                   = e
        case rewriteWithLimit 1 step (ConstE (IntegerC 1) :: Exp Double) of
          StepLimitReached (ConstE RationalC{}) -> pure ()
          result                                -> assertFailure $ show result
      it "detects a cycle containing NaN on the last permitted step" $
        let nan = ConstE (Const (0/0)) :: Exp Double
            step (NumUnopE Neg _) = NumUnopE Abs nan
            step _                = NumUnopE Neg nan
        in assertTerminates $ case rewriteWithLimit 2 step (NumUnopE Neg nan) of
          CycleDetected result -> sameExp result (NumUnopE Neg nan)
          _                    -> False
      it "stops a growing rewrite at its step budget" $
        let x = VarE "x" :: Exp Double
        in case rewriteWithLimit 3 (NumUnopE Neg) x of
          StepLimitReached result -> sameExp result (NumUnopE Neg (NumUnopE Neg (NumUnopE Neg x))) @?= True
          result                  -> assertFailure $ show result
      it "still stops when custom payload identity cannot recognize repetition" $
        case rewriteWithLimit 3 id (ConstE (Const Opaque)) of
          StepLimitReached _ -> pure ()
          result             -> assertFailure $ show result

-- Exercise bounded rewriting without a reflexive payload identity.
data Opaque = Opaque deriving (Show)

instance Eq Opaque where
    _ == _ = False

instance IsConst Opaque

assertTerminates :: Bool -> Assertion
assertTerminates condition = do
    result <- timeout 1000000 (evaluate condition)
    result @?= Just True

norvigTests :: Spec
norvigTests = do
    describe "Simplification tests from PAIP 8.2" $ do
        it "2 + 2 = 4" $
          simplify (2 + 2 :: Exp Double) @?= 4
        it "5 * 20 + 30 + 7 = 137" $
          simplify (5 * 20 + 30 + 7 :: Exp Double) @?= 137
        it "5 * x - (4 + 1) * x = 0" $
          simplify (5 * x - (4 + 1) * x :: Exp Double) @?= 0
        it "y / z * (5 * z - (4 + 1) * z) = 0" $
          simplify (y / z * (5 * z - (4 + 1) * z) :: Exp Double) @?= 0
        it "(4 - 3) * x + (y / y - 1) * z = x" $
          simplify ((4 - 3) * x + (y / y - 1) * z :: Exp Double) @?= x
    describe "Simplification tests from PAIP 8.3" $ do
        it "3 * 2 * x = 6 * x" $
          simplify (3 * 2 * x :: Exp Double) @?= 6 * x
        it "2 * x * x * 3 = 6 * x^2" $
          simplify (2 * x * x * 3 :: Exp Double) @?= 6 * NatPowE x 2
        it "2 * x * 3 * y * 4 * z * 5 * 6 = 720 * x * y * z" $
          simplify (2 * x * 3 * y * 4 * z * 5 * 6 :: Exp Double) @?= 720 * x * y * z
        it "3 + x + 4 + x = 2*x + 7" $
          simplify (3 + x + 4 + x :: Exp Double) @?= 2*x + 7
        it "2 * x * 3 * x * 4 * (1 / x) * 5 * 6 = 720 * x" $
          simplify (2 * x * 3 * x * 4 * ( 1 / x ) * 5 * 6 :: Exp Double) @?= 720 * x
  where
    x, y, z :: Exp a
    x = VarE "x"
    y = VarE "y"
    z = VarE "z"

prodTests :: SpecWith ()
prodTests =
    describe "product simplification" $ do
        it "x*(y/x) = y" $
          simplify (x*(y/x) :: Exp Double) @?= y
        it "(y/x)*x = y" $
          simplify ((y/x)*x :: Exp Double) @?= y
        it "(x*y)/x = y" $
          simplify ((x*y)/x :: Exp Double) @?= y
        it "(y*x)/x = y" $
          simplify ((y*x)/x :: Exp Double) @?= y
  where
    x, y :: Floating a => Exp a
    x = VarE "x"
    y = VarE "y"

powTests :: SpecWith ()
powTests =
    describe "exp/log/pow simplification" $ do
        it "recip (x ^ 3) = x ^^ (-3)" $
          simplify (FracUnopE Recip (NatPowE x 3) :: Exp Double) @?= IntPowE x (-3)
        it "x ^ 2 / x ^ 5 = x ^^ (-3)" $
          simplify (FracBinopE FDiv (NatPowE x 2) (NatPowE x 5) :: Exp Double) @?= IntPowE x (-3)
        it "x ^ 5 / x ^ 2 = x ^ 3" $
          simplify (FracBinopE FDiv (NatPowE x 5) (NatPowE x 2) :: Exp Double) @?= NatPowE x 3
        it "(x ^^ (-2)) ^ 3 = x ^^ (-6)" $
          simplify (NatPowE (IntPowE x (-2)) 3 :: Exp Double) @?= IntPowE x (-6)
        it "(x ^ 3) ^^ (-2) = x ^^ (-6)" $
          simplify (IntPowE (NatPowE x 3) (-2) :: Exp Double) @?= IntPowE x (-6)
        it "(x ^^ (-3)) ^^ (-2) = x ^ 6" $
          simplify (IntPowE (IntPowE x (-3)) (-2) :: Exp Double) @?= NatPowE x 6
        it "x ^ 2 * x ^^ (-5) = x ^^ (-3)" $
          simplify (NumBinopE Mul (NatPowE x 2) (IntPowE x (-5)) :: Exp Double) @?= IntPowE x (-3)
        it "x ^^ (-5) * x ^ 2 = x ^^ (-3)" $
          simplify (NumBinopE Mul (IntPowE x (-5)) (NatPowE x 2) :: Exp Double) @?= IntPowE x (-3)
        it "A nonnegative integral rational exponent becomes a natural power" $
          simplify (FracPowE x 3 :: Exp Double) @?= NatPowE x 3
        it "A negative integral rational exponent becomes an integer power" $
          simplify (FracPowE x (-3) :: Exp Double) @?= IntPowE x (-3)
        it "A rational constant exponent becomes a rational power" $
          simplify (FloatBinopE Pow x (ConstE (RationalC (1 / 2))) :: Exp Double) @?= FracPowE x (1 / 2)
        it "Preserves a square followed by a rational square root" $
          simplify (FracPowE (NatPowE x 2) (1 / 2) :: Exp Double) @?=
            FracPowE (NatPowE x 2) (1 / 2)
        it "Preserves a rational square root followed by a square" $
          simplify (NatPowE (FracPowE x (1 / 2)) 2 :: Exp Double) @?=
            NatPowE (FracPowE x (1 / 2)) 2
        it "Does not combine rational powers into an integral power" $
          simplify (NumBinopE Mul (FracPowE x (1 / 3)) (FracPowE x (2 / 3)) :: Exp Double)
            `shouldNotBe` x
        it "Does not divide rational powers into an integral power" $
          simplify (FracBinopE FDiv (FracPowE x (4 / 3)) (FracPowE x (1 / 3)) :: Exp Double)
            `shouldNotBe` x
        it "Combines identical rational powers as a square of the original expression" $
          simplify (NumBinopE Mul (FracPowE x (1 / 2)) (FracPowE x (1 / 2)) :: Exp Double) @?=
            NatPowE (FracPowE x (1 / 2)) 2
        it "Combines powers when their sum remains nonintegral" $
          simplify (NumBinopE Mul x (FracPowE x (1 / 2)) :: Exp Double) @?= FracPowE x (3 / 2)
        it "Terminates when ordering rational powers with constant bases" $
          property $ within 1000000 $
            eval (simplify (NumBinopE Mul (FracPowE 0 (1/2)) (FloatUnopE Sqrt 1)) :: Exp Double) === 0
        it "(sin x) ** 2 + (cos x) ** 2 = 1" $
          simplify (sin x ** 2 + cos x ** 2 :: Exp Double) @?= 1
  where
    x :: Floating a => Exp a
    x = VarE "x"

popEvalSimplifyEquiv :: Double -> Int -> DExp -> Property
popEvalSimplifyEquiv eps ms (DExp e) =
    counterexample (prettyCompact $ text "Expression:" <+> ppr e) $
    counterexample ("Expression: " ++ show e) $
    within ms $
    counterexample (prettyCompact $ text "Simplified:" <+> ppr e') $
    counterexample (prettyCompact $ text "Simplified and evaluated:" <+> ppr e1) $
    counterexample (prettyCompact $ text "Evaluated:" <+> ppr e2) $
    property (isExactE e') .&&. equiv eps e1 e2
  where
     e' = simplify e
     e1 = eval e'
     e2 = eval e

equiv :: Double -> Exp Double -> Exp Double -> Property
equiv eps (ConstE x) (ConstE y)
  | any nonfinite [eps, x', y'] || eps <= 0 = property False
  | d == 0                                  = property True
  | otherwise                               = property $ n / d < eps
  where
    x' = fromConst x
    y' = fromConst y
    n = abs (x' - y')
    d = max (abs x') (abs y')

    nonfinite a = isNaN a || isInfinite a

equiv _   e1         e2         = counterexample ("Expected finite constants: " ++ show (e1, e2)) False
