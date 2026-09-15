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
import           Data.Complex                    (Complex (..))
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
        it "log (e ** x) = x" $
          simplify (log (e ** x) :: Exp Double) @?= x
        it "e ** log x = x" $
          simplify (e ** log x :: Exp Double) @?= x
        it "(x ** y) * (x ** z) = x ** (y + z)" $
          simplify ((x ** y) * (x ** z) :: Exp Double) @?= x ** (y + z)
        it "(x ** y) / (x ** z) = x ** (y - z)" $
          simplify ((x ** y) / (x ** z) :: Exp Double) @?= x ** (y - z)
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
        it "log x + log y = log (x*y)" $
          simplify (log x + log y :: Exp Double) @?= log (x*y)
        it "log x - log y = log (x/y)" $
          simplify (log x - log y :: Exp Double) @?= log (x/y)
        it "(sin x) ** 2 + (cos x) ** 2 = 1" $
          simplify (sin x ** 2 + cos x ** 2 :: Exp Double) @?= 1
  where
    e, x, y, z :: Floating a => Exp a
    e = ConstE E
    x = VarE "x"
    y = VarE "y"
    z = VarE "z"

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
