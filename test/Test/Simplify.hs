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
             ("nearby values", 1, 1 + 1e-13),
             ("rounding residue beside zero", -0.0, -4.440892098500626e-16)] $ \(name, x, y) ->
        it ("accepts " ++ name) $
          equiv eps (ConstE (Const x)) (ConstE (Const y))
      forM_ [("unequal finite values", 1, 2), ("a small value beside zero", 0, 1e-6),
             ("large values beyond the relative tolerance", 1e6, 1e6 + 1)] $ \(name, x, y) ->
        it ("rejects " ++ name) $
          expectFailure $ equiv eps (ConstE (Const x)) (ConstE (Const y))
      it "preserves evaluation when simplification cancels to rounding residue" $
        popEvalSimplifyEquiv eps tensec (DExp cancellingQuotient)
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
    zeroProductTests
    denominatorCancellationTests
    cancellationDomainTests
    trigonometricDomainTests
    inverseDomainTests
    exactNegationTests
    oppositeTermTests
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

trigonometricDomainTests :: Spec
trigonometricDomainTests = describe "Cancellation in trigonometric identities" $ do
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) -> do
      it (name ++ " preserves nonfinite variable arguments") $
        forM_ [0/0, 1/0, -1/0] $ \payload ->
          assertNaN (eval (at payload (transform (identity (VarE "x")))))
      it (name ++ " preserves nonfinite constant arguments") $
        forM_ [0/0, 1/0, -1/0] $ \payload ->
          assertNaN (eval (transform (identity (ConstE (Const payload)))))
      forM_ [("reciprocal", FracUnopE Recip (VarE "x")),
             ("logarithm", FloatUnopE Log (VarE "x"))] $ \(form, argument) ->
        it (name ++ " retains the " ++ form ++ " argument's zero failure") $ do
          let e = identity argument
          assertNaN (eval (at 0 e))
          assertNaN (eval (at 0 (transform e)))
          assertBool (show e) (abs (value (at 2 (transform e)) - 1) < 1e-12)
      it (name ++ " retains explicit exceptional arguments") $
        forM_ [Undefined, Infty, NegInfty] $ \argument ->
          let e = identity argument :: Exp Double
          in sameExp (transform e) e @?= True
      it (name ++ " still reduces identities at exact constant arguments") $
        forM_ [IntegerC 1, RationalC (1/3), Pi 1, E] $ \argument ->
          transform (identity (ConstE argument) :: Exp Double) @?= 1
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) -> do
      it (name ++ " retains complex reciprocal failures") $ do
        let e = transform (identity (FracUnopE Recip (VarE "x"))) :: Exp (Complex Double)
        assertBool (show e) (isNaN (magnitude (value (at 0 e))))
        assertBool (show e) (magnitude (value (at (1 :+ 1) e) - 1) < 1e-12)
      it (name ++ " still reduces identities at complex exact arguments") $
        transform (identity (ConstE E) :: Exp (Complex Double)) @?= 1
  where
    identity :: (Floating a, Floating (Const a), IsConst a, Eq a) => Exp a -> Exp a
    identity argument = NumBinopE Add (NatPowE (sin argument) 2) (NatPowE (cos argument) 2)

    at :: (Eq a, Num a, IsConst a) => a -> Exp a -> Exp a
    at payload = mapExp $ \e -> case e of
                                 VarE "x" -> ConstE (Const payload)
                                 _        -> e

    value :: (Eq a, IsConst a) => Exp a -> a
    value e = case eval e of
                ConstE c -> fromConst c
                _        -> error "Expected a constant after evaluation"

    assertNaN :: Exp Double -> Assertion
    assertNaN e = assertBool (show e) (isNaN (value e))

zeroProductTests :: Spec
zeroProductTests = describe "Zero products" $ do
    forM_ [("construction", id), ("evalexact", evalexact)] $ \(name, transform) ->
      forM_ [("left", (0*)), ("right", (*0))] $ \(side, productWithZero) ->
        it (name ++ " preserves rational zero-division failures on the " ++ side) $ do
          let e = transform (productWithZero (FracUnopE Recip (VarE "x")))
          evaluate (rationalValue (at 0 e)) `shouldThrow` anyArithException
          rationalValue (at 2 e) @?= 0
    forM_ [("construction", id), ("evalexact", evalexact)] $ \(name, transform) ->
      forM_ [("left", NumBinopE Mul 0), ("right", \e -> NumBinopE Mul e 0)] $ \(side, productWithZero) -> do
        it (name ++ " preserves nonfinite variable values on the " ++ side) $
          forM_ [0/0, 1/0, -1/0] $ \payload ->
            assertNaN (eval (at payload (transform (productWithZero (VarE "x")))))
        it (name ++ " preserves exceptional leaves on the " ++ side) $
          forM_ [Undefined, Infty, NegInfty] $ \leaf ->
            transform (productWithZero leaf) `shouldNotBe` (0 :: Exp Double)
    forM_ [0/0, 1/0, -1/0] $ \payload ->
      it ("preserves nonfinite payloads during construction: " ++ show payload) $
        forM_ [0 * ConstE (Const payload), ConstE (Const payload) * 0] $ \e ->
          assertNaN (eval e)
    it "still reduces zero products with explicit exact constants" $
      forM_ [IntegerC 2, RationalC (3/2), Pi 1, E] $ \c ->
        forM_ [NumBinopE Mul 0 (ConstE c), NumBinopE Mul (ConstE c) 0] $ \e ->
          simplify (e :: Exp Double) @?= 0
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) ->
      forM_ [("left", NumBinopE Mul 0), ("right", \e -> NumBinopE Mul e 0)] $ \(side, productWithZero) -> do
        it (name ++ " reduces a symbolic zero product on the " ++ side) $
          sameExp (transform (productWithZero (VarE "x")) :: Exp Rational) 0 @?= True
        it (name ++ " extends a rational zero product's domain on the " ++ side) $ do
          let source = productWithZero (FracUnopE Recip (VarE "x"))
              result = transform source
          evaluate (rationalValue (at 0 source)) `shouldThrow` anyArithException
          sameExp result 0 @?= True
          rationalValue (at 0 result) @?= 0
          forM_ [-2, -1/3, 1/3, 2] $ \point ->
            rationalValue (at point result) @?= rationalValue (at point source)
    it "reduces symbolic zero products with only Num operations" $
      forM_ [simp, simplify, simplify'] $ \transform ->
        forM_ [NumBinopE Mul 0 (VarE "x"), NumBinopE Mul (VarE "x") 0] $ \source ->
          sameExp (transform source :: Exp Integer) 0 @?= True
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) ->
      forM_ [("left", NumBinopE Mul 0), ("right", \e -> NumBinopE Mul e 0)] $ \(side, productWithZero) ->
        it (name ++ " permits zero annihilation of exceptional operands on the " ++ side) $
          forM_ [Undefined, Infty, NegInfty,
                 ConstE (Const (0/0)), ConstE (Const (1/0)), ConstE (Const (-1/0))] $ \operand ->
            sameExp (transform (productWithZero operand) :: Exp Double) 0 @?= True
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) ->
      it (name ++ " preserves complex zero products on their source domain") $
        forM_ [NumBinopE Mul 0 (FracUnopE Recip (VarE "x")),
               NumBinopE Mul (FracUnopE Recip (VarE "x")) 0] $ \source -> do
          let result = transform source :: Exp (Complex Double)
          sameExp result 0 @?= True
          forM_ [1 :+ 1, (-2) :+ 3] $ \point ->
            eval (at point result) @?= eval (at point source)
  where
    at :: (Eq a, Num a, IsConst a) => a -> Exp a -> Exp a
    at payload = mapExp $ \e -> case e of
                                 VarE "x" -> ConstE (Const payload)
                                 _        -> e

    rationalValue :: Exp Rational -> Rational
    rationalValue e = case eval e of
                        ConstE c -> fromConst c
                        result   -> error (show result)

    assertNaN :: Exp Double -> Assertion
    assertNaN (ConstE c) = assertBool (show c) (isNaN (fromConst c))
    assertNaN e          = assertFailure (show e)

oppositeTermTests :: Spec
oppositeTermTests = describe "Cancellation of opposite terms" $ do
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) ->
      forM_ (oppositeForms (FracUnopE Recip (VarE "x"))) $ \(form, e) ->
        it (name ++ " permits domain extension in " ++ form) $ do
          evaluate (rationalValue (at 0 e)) `shouldThrow` anyArithException
          sameExp (transform e) 0 @?= True
          rationalValue (at 0 (transform e)) @?= 0
          forM_ [-2, -1/3, 1/3, 2] $ \point ->
            rationalValue (at point (transform e)) @?= rationalValue (at point e)
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) -> do
      forM_ (oppositeForms (VarE "x")) $ \(form, e) ->
        it (name ++ " cancels symbolic operands in " ++ form) $ do
          sameExp (transform e :: Exp Double) 0 @?= True
          forM_ [0/0, 1/0, -1/0] $ \value -> do
            assertNaN (eval (at value e))
            sameExp (eval (at value (transform e))) 0 @?= True
      it (name ++ " cancels identical nonfinite constant payloads") $
        forM_ [0/0, 1/0, -1/0] $ \value ->
          forM_ (oppositeForms (ConstE (Const value))) $ \(_, e) ->
            sameExp (transform e) 0 @?= True
      it (name ++ " cancels identical exceptional leaves") $
        forM_ [Undefined, Infty, NegInfty] $ \value ->
          forM_ (oppositeForms value) $ \(_, e) ->
            sameExp (transform e :: Exp Double) 0 @?= True
      it (name ++ " still cancels explicit exact constants") $
        forM_ [IntegerC 3, RationalC (3/2), Pi 1, Pi (-1), E] $ \value ->
          transform (NumBinopE Sub (ConstE value) (ConstE value) :: Exp Double) @?= 0
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) ->
      forM_ (oppositeForms (FracUnopE Recip (VarE "x"))) $ \(form, e) ->
        it (name ++ " preserves complex values on the source domain in " ++ form) $ do
          sameExp (transform e :: Exp (Complex Double)) 0 @?= True
          forM_ [1 :+ 1, (-2) :+ 3] $ \point ->
            eval (at point (transform e)) @?= eval (at point e)
    it "cancels symbolic opposites with only Num operations" $
      forM_ [simp, simplify, simplify'] $ \transform ->
        forM_ (oppositeForms (VarE "x")) $ \(_, e) ->
          sameExp (transform e :: Exp Integer) 0 @?= True
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) ->
      it (name ++ " does not cancel unequal operands") $
        let x = VarE "x"
            y = NumBinopE Add x 1
        in forM_ [NumBinopE Sub x y, NumBinopE Add x (NumUnopE Neg y),
                  NumBinopE Add (NumUnopE Neg x) y] $ \e ->
             forM_ [-2, 0, 2] $ \point ->
               rationalValue (at point (transform e)) @?= rationalValue (at point e)
    it "retains reciprocal exclusions during construction" $
      let u = FracUnopE Recip (VarE "x")
      in forM_ [u-u, u+(-u), (-u)+u] $ \e ->
           evaluate (rationalValue (at 0 e)) `shouldThrow` anyArithException
    forM_ (oppositeForms (FracUnopE Recip (VarE "x"))) $ \(form, e) ->
      it ("evalexact retains reciprocal exclusions in " ++ form) $
        evaluate (rationalValue (at 0 (evalexact e))) `shouldThrow` anyArithException
    it "retains nonfinite arithmetic during construction and exact evaluation" $
      forM_ [0/0, 1/0, -1/0] $ \payload ->
        let u = ConstE (Const payload)
        in do
          forM_ [u-u, u+(-u), (-u)+u] $ \e -> assertNaN (eval e)
          forM_ (oppositeForms u) $ \(_, e) -> assertNaN (eval (evalexact e))
  where
    oppositeForms :: Num a => Exp a -> [(String, Exp a)]
    oppositeForms e =
      [ ("u - u", NumBinopE Sub e e)
      , ("u + (-u)", NumBinopE Add e (NumUnopE Neg e))
      , ("(-u) + u", NumBinopE Add (NumUnopE Neg e) e)
      ]

    at :: (Eq a, Num a, IsConst a) => a -> Exp a -> Exp a
    at value = mapExp $ \e -> case e of
                               VarE "x" -> ConstE (Const value)
                               _        -> e

    rationalValue :: Exp Rational -> Rational
    rationalValue e = case eval e of
                        ConstE c -> fromConst c
                        result   -> error (show result)

    assertNaN :: Exp Double -> Assertion
    assertNaN (ConstE c) = assertBool (show c) (isNaN (fromConst c))
    assertNaN e          = assertFailure (show e)

inverseDomainTests :: Spec
inverseDomainTests = describe "Cancellation of nested inverses" $ do
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) ->
      forM_ inverseForms $ \(caseName, e) ->
        it (name ++ " preserves rational division by zero in " ++ caseName) $ do
          evaluate (rationalValue (atZero e)) `shouldThrow` anyArithException
          evaluate (rationalValue (atZero (transform e))) `shouldThrow` anyArithException
          rationalValue (atTwo (transform e)) @?= rationalValue (atTwo e)
    forM_ inverseForms $ \(caseName, e) ->
      it ("preserves complex zero failures in " ++ caseName) $
        case eval (atZero (simplify e)) :: Exp (Complex Double) of
          ConstE c -> samePayload (fromConst c) ((0/0) :+ (0/0)) @?= True
          result   -> assertFailure (show result)
    it "still reduces nested inverses of explicit nonzero constants" $
      forM_ [IntegerC 2, IntegerC (-2), RationalC (3/2), Pi 1, E] $ \c ->
        simp (FracUnopE Recip (FracUnopE Recip (ConstE c)) :: Exp Double) @?= ConstE c
    it "still flattens negative powers of a known nonzero named constant" $
      simplify (IntPowE (IntPowE (ConstE E) (-3)) (-2) :: Exp Double) @?= NatPowE (ConstE E) 6
  where
    inverseForms :: Fractional a => [(String, Exp a)]
    inverseForms =
      [ ("recip (recip x)", FracUnopE Recip (FracUnopE Recip x))
      , ("(x^^(-1))^^(-1)", IntPowE (IntPowE x (-1)) (-1))
      , ("(x^^(-3))^^(-2)", IntPowE (IntPowE x (-3)) (-2))
      , ("recip (x^^(-2))", FracUnopE Recip (IntPowE x (-2)))
      ]
      where
        x = VarE "x"

    atZero, atTwo :: (Eq a, Num a, IsConst a) => Exp a -> Exp a
    atZero = mapExp $ \e -> case e of
                            VarE "x" -> ConstE (IntegerC 0)
                            _        -> e
    atTwo = mapExp $ \e -> case e of
                           VarE "x" -> ConstE (IntegerC 2)
                           _        -> e

    rationalValue :: Exp Rational -> Rational
    rationalValue e = case eval e of
                        ConstE c -> fromConst c
                        result   -> error (show result)

denominatorCancellationTests :: Spec
denominatorCancellationTests = describe "Algebraic denominator cancellation" $ do
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) ->
      forM_ expressions $ \(caseName, e, expected) ->
        it (name ++ " cancels " ++ caseName ++ " on the source domain") $ do
          sameExp (transform e) expected @?= True
          forM_ [-3, -1, 1, 2] $ \value ->
            eval (at value (transform e)) @?= eval (at value e)
          evaluate (rationalValue (at 0 e)) `shouldThrow` anyArithException
          rationalValue (at 0 (transform e)) @?= rationalValue (at 0 expected)
    forM_ expressions $ \(caseName, e, _) ->
      it ("evalexact retains the zero exclusion in " ++ caseName) $
        evaluate (rationalValue (at 0 (evalexact e))) `shouldThrow` anyArithException
    it "retains unknown quotients during construction" $ do
      sameExp (x / x) (FracBinopE FDiv x x) @?= True
      sameExp (0 / x) (FracBinopE FDiv 0 x) @?= True
    forM_ [("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) ->
      it (name ++ " cancels x*recip x after exposing the quotient") $ do
        let e = NumBinopE Mul x (FracUnopE Recip x)
        sameExp (transform e) 1 @?= True
        forM_ [-2, 2] $ \value ->
          eval (at value (transform e)) @?= eval (at value e)
        evaluate (rationalValue (at 0 e)) `shouldThrow` anyArithException
    it "cancels matching complex factors without a positivity assumption" $ do
      let cx = VarE "x" :: Exp (Complex Double)
          cy = VarE "y"
          e = FracBinopE FDiv (NumBinopE Mul cx cy) cx
      sameExp (simplify e) cy @?= True
      eval (at (0 :+ 2) (simplify e)) @?= eval (at (0 :+ 2) e)
    it "does not cancel different factors" $
      sameExp (simp (FracBinopE FDiv (NumBinopE Mul x y) (VarE "z")))
              (FracBinopE FDiv (NumBinopE Mul x y) (VarE "z")) @?= True
    it "allows domain extension for identical nonfinite and exceptional operands" $
      forM_ [ConstE (Const (1/0)), ConstE (Const (0/0)), Undefined, Infty, NegInfty] $ \e ->
        sameExp (simp (FracBinopE FDiv e e) :: Exp Double) 1 @?= True
  where
    x, y :: Exp Rational
    x = VarE "x"
    y = VarE "y"

    expressions :: [(String, Exp Rational, Exp Rational)]
    expressions =
      [ ("0/x", FracBinopE FDiv 0 x, 0)
      , ("x/x", FracBinopE FDiv x x, 1)
      , ("x*(y/x)", NumBinopE Mul x (FracBinopE FDiv y x), y)
      , ("(y/x)*x", NumBinopE Mul (FracBinopE FDiv y x) x, y)
      , ("(x*y)/x", FracBinopE FDiv (NumBinopE Mul x y) x, y)
      , ("(y*x)/x", FracBinopE FDiv (NumBinopE Mul y x) x, y)
      ]

    at :: (Eq a, Num a, IsConst a) => a -> Exp a -> Exp a
    at value = mapExp $ \e -> case e of
                               VarE "x" -> ConstE (Const value)
                               VarE "y" -> 3
                               _        -> e

    rationalValue :: Exp Rational -> Rational
    rationalValue e = case eval e of
                       ConstE c -> fromConst c
                       result   -> error (show result)

cancellationDomainTests :: Spec
cancellationDomainTests = describe "Cancellation domains" $ do
    forM_ [("simp", simp), ("simplify", simplify), ("simplify'", simplify')] $ \(name, transform) ->
      forM_ expressions $ \(caseName, e) ->
        it (name ++ " preserves the zero-denominator failure in " ++ caseName) $ do
          assertNaN (eval (at 0 e))
          assertNaN (eval (at 0 (transform e)))
          eval (at 2 (transform e)) @?= eval (at 2 e)
    it "still cancels explicit nonzero exact factors" $
      forM_ [IntegerC 2, IntegerC (-2), RationalC (3/2), Pi 1, Pi (-1), E] $ \c -> do
        let k = ConstE c :: Exp Double
        simplify (FracBinopE FDiv k k) @?= 1
        simplify (FracBinopE FDiv 0 k) @?= 0
        simplify (FracBinopE FDiv (NumBinopE Mul k y) k) @?= y
  where
    x, y :: Exp Double
    x = VarE "x"
    y = VarE "y"

    expressions :: [(String, Exp Double)]
    expressions =
      [ ("x^5/x^2", FracBinopE FDiv (NatPowE x 5) (NatPowE x 2))
      , ("x^2/x^5", FracBinopE FDiv (NatPowE x 2) (NatPowE x 5))
      , ("x^2*x^^(-1)", NumBinopE Mul (NatPowE x 2) (IntPowE x (-1)))
      , ("2*x^2*x^^(-1)", NumBinopE Mul (NumBinopE Mul 2 (NatPowE x 2)) (IntPowE x (-1)))
      , ("fractional-power quotient", FracBinopE FDiv (FracPowE x (5/2)) (FracPowE x (1/2)))
      , ("fractional and integer quotient", FracBinopE FDiv (FracPowE x (5/2)) x)
      , ("fractional and negative power product", NumBinopE Mul (FracPowE x (5/2)) (IntPowE x (-1)))
      ]

    at :: Double -> Exp Double -> Exp Double
    at value = mapExp replace
      where
        replace (VarE "x") = ConstE (Const value)
        replace (VarE "y") = 2
        replace e          = e

    assertNaN :: Exp Double -> Assertion
    assertNaN (ConstE c) = assertBool (show c) (isNaN (fromConst c))
    assertNaN e          = assertFailure (show e)

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
    it "terminates when algebraic cancellation removes NaN operands" $
      let nan = ConstE (Const (0/0)) :: Exp Double
      in assertTerminates $ sameExp (simplify (NumBinopE Sub nan nan)) 0

    describe "Products of powers with constant bases" $
      -- Each power once moved ahead of any product or quotient, including one
      -- containing the other power, so factor reordering cycled.
      forM_ [ ("with a constant quotient", constPowQuotient)
            , ("with a constant coefficient", constPowCoefficient)
            ] $ \(name, e) -> do
        it ("reaches a fixed point " ++ name) $
          case simplifyWithLimit 100 e of
            FixedPoint{} -> pure ()
            result       -> assertFailure $ show result
        forM_ [("simplify", simplify), ("simplify'", simplify')] $ \(simplifierName, simplifyWith) ->
          it (simplifierName ++ " terminates " ++ name) $
            assertTerminates $ isExactE (simplifyWith e)

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

-- (abs (1 + acos 1) - 1) / recip (-4 + (-1)/(-5)) evaluates to -0.0, but its
-- simplified form evaluates to a rounding residue near -4.4e-16.
cancellingQuotient :: Exp Double
cancellingQuotient =
    FracBinopE FDiv
      (NumBinopE Sub
        (NumUnopE Abs (NumBinopE Add (ConstE (IntegerC 1)) (FloatUnopE Acos (ConstE (RationalC 1)))))
        (ConstE (RationalC 1)))
      (FracUnopE Recip
        (NumBinopE Add
          (ConstE (IntegerC (-4)))
          (FracBinopE FDiv (NumUnopE Neg (ConstE (IntegerC 1))) (ConstE (IntegerC (-5))))))

-- 0 ** (1/5) * sqrt ((-1)/(-2)) / 3
constPowQuotient :: Exp Double
constPowQuotient =
    FracBinopE FDiv
      (NumBinopE Mul
        (FracPowE (ConstE (IntegerC 0)) (1/5))
        (FloatUnopE Sqrt (FracBinopE FDiv (ConstE (IntegerC (-1))) (ConstE (IntegerC (-2))))))
      (ConstE (IntegerC 3))

-- 2 ** (1/3) * ((-134/9) * 1 ** (3/2))
constPowCoefficient :: Exp Double
constPowCoefficient =
    NumBinopE Mul
      (FracPowE (ConstE (IntegerC 2)) (1/3))
      (NumBinopE Mul (ConstE (RationalC (-134/9))) (FracPowE (ConstE (RationalC 1)) (3/2)))

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
        it "collects coefficients without cancelling the reciprocal in 2*x*3*x*4*(1/x)*5*6" $
          simplify (2 * x * 3 * x * 4 * (1/x) * 5 * 6 :: Exp Double) @?=
            720 * IntPowE x (-1) * NatPowE x 2
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
        it "preserves the denominator in x ^ 2 / x ^ 5" $
          let e = FracBinopE FDiv (NatPowE x 2) (NatPowE x 5) :: Exp Double
          in sameExp (simplify e) e @?= True
        it "preserves the denominator in x ^ 5 / x ^ 2" $
          let e = FracBinopE FDiv (NatPowE x 5) (NatPowE x 2) :: Exp Double
          in sameExp (simplify e) e @?= True
        it "(x ^^ (-2)) ^ 3 = x ^^ (-6)" $
          simplify (NatPowE (IntPowE x (-2)) 3 :: Exp Double) @?= IntPowE x (-6)
        it "(x ^ 3) ^^ (-2) = x ^^ (-6)" $
          simplify (IntPowE (NatPowE x 3) (-2) :: Exp Double) @?= IntPowE x (-6)
        it "preserves both negative powers in (x ^^ (-3)) ^^ (-2)" $
          let e = IntPowE (IntPowE x (-3)) (-2) :: Exp Double
          in sameExp (simplify e) e @?= True
        it "preserves the zero singularity in x ^ 2 * x ^^ (-5)" $
          simplify (NumBinopE Mul (NatPowE x 2) (IntPowE x (-5)) :: Exp Double) @?=
            FracBinopE FDiv (NatPowE x 2) (NatPowE x 5)
        it "preserves the zero singularity in x ^^ (-5) * x ^ 2" $
          simplify (NumBinopE Mul (IntPowE x (-5)) (NatPowE x 2) :: Exp Double) @?=
            FracBinopE FDiv (NatPowE x 2) (NatPowE x 5)
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
        it "normalizes powers without cancelling an unknown trigonometric argument" $
          simplify (sin x ** 2 + cos x ** 2 :: Exp Double) @?=
            NatPowE (sin x) 2 + NatPowE (cos x) 2
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

-- Compare by relative error with an absolute floor at unit scale. Reordered
-- floating-point operations can cancel to a residue near the rounding error of
-- their unit-scale operands, even when the reference result is exactly zero.
equiv :: Double -> Exp Double -> Exp Double -> Property
equiv eps (ConstE x) (ConstE y)
  | any nonfinite [eps, x', y'] || eps <= 0 = property False
  | otherwise                               = property $ n < eps * max 1 d
  where
    x' = fromConst x
    y' = fromConst y
    n = abs (x' - y')
    d = max (abs x') (abs y')

    nonfinite a = isNaN a || isInfinite a

equiv _   e1         e2         = counterexample ("Expected finite constants: " ++ show (e1, e2)) False
