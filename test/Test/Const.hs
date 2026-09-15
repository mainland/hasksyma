{-# LANGUAGE CPP                        #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}

-- |
-- Module      :  Test.Const
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Const where

#if defined(CYCLOTOMIC)
import           Control.Exception (evaluate)
import           Test.Hspec        (errorCall, shouldThrow)
#endif
import           Control.Monad     (forM_)
import           Data.Complex      (Complex (..))
import           Data.List         (permutations)
import           Data.Proxy        (Proxy (Proxy))
import qualified Data.Set          as Set
import           Test.Hspec        (Spec, describe, it, shouldBe)
import           Test.QuickCheck

import           Hasksyma.Const
import qualified Hasksyma.Exp      as Exp
import           Hasksyma.Simplify (simplify)
import           Test.Arbitrary    ()

-- Exercise the class defaults without a type-specific constant interpreter.
newtype WithDefaultConst a = WithDefaultConst a
    deriving (Eq, Ord, Show, Num, Fractional, Floating, Real, RealFrac, RealFloat)

instance IsConst (WithDefaultConst a)

class (Eq a, Show a) => Equiv a where
    equiv :: a -> a -> Property
    equiv = (===)

instance Equiv Integer where

instance Equiv Rational where

instance Equiv Float where
    x `equiv` y
       | x == 0    = property $ x == y
       | otherwise = counterexample ("abs (" ++ show x ++ " - " ++ show y ++ ")/" ++ show x ++ " == " ++ show diff) (diff < eps)
      where
        x', y' :: Rational
        x' = toRational x
        y' = toRational y

        diff, eps :: Float
        diff = fromRational (abs (x' - y') / max x' y')
        eps = 1e-3

instance Equiv Double where
    x `equiv` y
       | x == 0    = property $ x == y
       | otherwise = counterexample ("abs (" ++ show x ++ " - " ++ show y ++ ")/" ++ show x ++ " == " ++ show diff) (diff < eps)
      where
        x', y' :: Rational
        x' = toRational x
        y' = toRational y

        diff, eps :: Float
        diff = fromRational (abs (x' - y') / max x' y')
        eps = 1e-11

data NumBinop = NumBinop String (forall a . Num a => a -> a -> a)

instance Show NumBinop where
    show (NumBinop op _) = op

instance Arbitrary NumBinop where
    arbitrary = elements [NumBinop "(+)" (+), NumBinop "(-)" (-), NumBinop "(*)" (*)]

prop_num_equiv :: (IsConst a, Num a, Equiv a)
               => proxy a
               -> NumBinop -> Const a -> Const a -> Property
prop_num_equiv _ (NumBinop _ f) x y = fromConst (f x y) `equiv` f (fromConst x) (fromConst y)

prop_integral_exact :: (forall a . Integral a => a -> a -> a)
                    -> Integer -> NonZero Integer -> Property
prop_integral_exact f x (NonZero y) = within 1000000 $
    case f (IntegerC x :: Const Integer) (IntegerC y) of
      IntegerC z -> z === f x y
      z          -> counterexample ("Expected an exact integer, got " ++ show z) False

data FracBinop = FracBinop String (forall a . Fractional a => a -> a -> a) (forall a . (Eq a, Fractional a) => a -> a -> Bool)

instance Show FracBinop where
    show (FracBinop op _ _) = op

instance Arbitrary FracBinop where
    arbitrary = pure $ FracBinop "(/)" (/) (\_ y -> y /= 0)

prop_frac_equiv :: (IsConst a, Fractional a, Equiv a)
                => proxy a
                -> FracBinop -> Const a -> Const a -> Property
prop_frac_equiv _ (FracBinop _ f p) x y = p (fromConst x) (fromConst y) ==> fromConst (f x y) `equiv` f (fromConst x) (fromConst y)

data FloatUnop = FloatUnop String (forall a . Floating a => a -> a) (forall a . (Ord a, Floating a) => a -> Bool)

instance Show FloatUnop where
    show (FloatUnop op _ _) = op

instance Arbitrary FloatUnop where
    arbitrary = elements [ FloatUnop "exp" exp (const True)
                         , FloatUnop "log" log (const True)
                         , FloatUnop "sqrt" sqrt (>= 0)
                         , FloatUnop "sin" sin (const True)
                         , FloatUnop "cos" cos (const True)
                         , FloatUnop "tan" tan (const True)
                         , FloatUnop "asin" asin (const True)
                         , FloatUnop "acos" acos (const True)
                         , FloatUnop "atan" atan (const True)
                         , FloatUnop "sinh" sinh (const True)
                         , FloatUnop "cosh" cosh (const True)
                         , FloatUnop "tanh" tanh (const True)
                         , FloatUnop "asinh" asinh (const True)
                         , FloatUnop "acosh" acosh (const True)
                         , FloatUnop "atanh" atanh (const True)
                         ]

prop_float_equiv :: (IsConst a, Floating a, Equiv a, Ord a, Floating (Const a))
                 => proxy a
                 -> FloatUnop -> Const a -> Property
prop_float_equiv _ (FloatUnop _ f p ) x = p (fromConst x) ==> fromConst (f x) `equiv` f (fromConst x)

data FloatBinop = FloatBinop String (forall a . Floating a => a -> a -> a) (forall a . (Ord a, Floating a) => a -> a -> Bool)

instance Show FloatBinop where
    show (FloatBinop op _ _) = op

instance Arbitrary FloatBinop where
    arbitrary = elements [ FloatBinop "(**)" (**) (\x y -> x /= 0 || y /= 0)
                         , FloatBinop "logBase" logBase (\x y -> x > 1 && y /= 0)
                         ]

prop_float2_equiv :: (IsConst a, Floating a, Equiv a, Ord a, Floating (Const a))
                  => proxy a
                  -> FloatBinop -> Const a -> Const a -> Property
prop_float2_equiv _ (FloatBinop _ f p) x y = p (fromConst x) (fromConst y) ==> fromConst (f x y) `equiv` f (fromConst x) (fromConst y)

constTests :: Spec
constTests = describe "Computations with constants" $ do
    describe "Rewrite identity" $ do
      it "recognizes Float and Double NaNs without changing equality" $ do
        let nan = Const (0/0) :: Const Double
        sameConst nan nan `shouldBe` True
        (nan == nan) `shouldBe` False
        sameConst (Const (0/0) :: Const Float) (Const (0/0)) `shouldBe` True
      it "distinguishes signed zeros and non-NaN payloads" $ do
        sameConst (Const (-0.0) :: Const Double) (Const 0) `shouldBe` False
        sameConst (Const (0/0) :: Const Double) (Const 1) `shouldBe` False
      it "compares both components of complex NaN payloads" $ do
        let nan = 0/0 :: Double
        sameConst (Const (nan :+ 1)) (Const (nan :+ 1)) `shouldBe` True
        sameConst (Const (nan :+ 1)) (Const (nan :+ 2)) `shouldBe` False
        sameConst (Const (1 :+ nan)) (Const (2 :+ nan)) `shouldBe` False
      it "keeps equal numeric representations distinct" $ do
        sameConst (IntegerC 1 :: Const Double) (RationalC 1) `shouldBe` False
        sameConst (Const 1 :: Const Double) (IntegerC 1) `shouldBe` False
        sameConst (Pi 0 :: Const Double) (IntegerC 0) `shouldBe` False
      it "uses payload equality by default for custom types" $
        sameConst (Const (WithDefaultConst True)) (Const (WithDefaultConst True)) `shouldBe` True
#if defined(CYCLOTOMIC)
      it "compares cyclotomic payloads without merging constant constructors" $ do
        let r = RealCycC 2 :: Const Double
            c = CycC 2 :: Const (Complex Double)
        sameConst r r `shouldBe` True
        sameConst c c `shouldBe` True
        sameConst r (RationalC 2) `shouldBe` False
        sameConst c (RationalC 2) `shouldBe` False
#endif
    describe "Constant comparison" $ do
      it "keeps symbolic pi distinct from nearby exact rationals" $ do
        let a = RationalC (toRational (pi :: Double)) :: Const Double
            b = Pi 1
            c = RationalC (toRational (pi :: Double) + 1/100000000000000000000)
        (a == b, b == c, a == c) `shouldBe` (False, False, False)
        forM_ (permutations [a, b, c]) $ \xs ->
          Set.size (Set.fromList xs) `shouldBe` 3
      it "compares pi coefficients exactly even when they round alike" $
        (Pi 1 == (Pi (1 + 1/100000000000000000000) :: Const Double)) `shouldBe` False
      it "does not equate named constants with evaluated approximations" $ do
        (Pi 1 == Const (pi :: Double)) `shouldBe` False
        (E == Const (exp 1 :: Double)) `shouldBe` False
      it "preserves exact rational equivalences" $ do
        (IntegerC 2 :: Const Double) `shouldBe` RationalC 2
        (Pi 0 :: Const Double) `shouldBe` IntegerC 0
      it "compares evaluated floats by their exact binary rational values" $ do
        (Const 0.5 :: Const Double) `shouldBe` RationalC (1/2)
        isExact (Const 0.5 :: Const Double) `shouldBe` False
        (Const 0.1 == (RationalC (1/10) :: Const Double)) `shouldBe` False
        (Const 0.1 :: Const Double) `shouldBe` RationalC (toRational (0.1 :: Double))
      it "does not round large exact integers to compare them with floats" $
        (Const 9007199254740992 == (IntegerC 9007199254740993 :: Const Double)) `shouldBe` False
      it "does not wrap exact integers to compare them with Int payloads" $
        (Const (minBound :: Int) == IntegerC (toInteger (maxBound :: Int) + 1)) `shouldBe` False
      it "supports exact rational values in real complex payloads" $ do
        (Const (0.5 :+ 0) :: Const (Complex Double)) `shouldBe` RationalC (1/2)
        (Const (0.5 :+ 1) == (RationalC (1/2) :: Const (Complex Double))) `shouldBe` False
      it "keeps opaque user payloads separate from exact syntax" $
        (Const (WithDefaultConst (1 :: Integer)) == IntegerC 1) `shouldBe` False
      it "retains the payload equality policy for NaNs and signed zeros" $ do
        let nan = Const (0/0) :: Const Double
        (nan == nan) `shouldBe` False
        (Const (-0.0) :: Const Double) `shouldBe` Const 0
      it "orders infinities without converting them to rationals" $ do
        let values = [Const (-1/0), IntegerC 0, Const (1/0)] :: [Const Double]
        forM_ (permutations values) $ \xs ->
          Set.size (Set.fromList xs) `shouldBe` 3
      it "does not cancel the difference between pi and a rational approximation" $ do
        let e = Exp.NumBinopE Exp.Sub (Exp.ConstE (Pi 1))
                  (Exp.ConstE (RationalC (toRational (pi :: Double))))
                  :: Exp.Exp Double
        (simplify e == Exp.ConstE (IntegerC 0)) `shouldBe` False
      it "inherits consistent constant identity in expression keys" $ do
        let values = map Exp.ConstE [Pi 1, Const pi, RationalC (toRational (pi :: Double))]
                       :: [Exp.Exp Double]
        Set.size (Set.fromList values) `shouldBe` 2
      it "satisfies comparison laws for Float constants" $
        property (comparisonLaws :: Const Float -> Const Float -> Const Float -> Property)
      it "satisfies comparison laws for Double constants" $
        property (comparisonLaws :: Const Double -> Const Double -> Const Double -> Property)
      it "satisfies comparison laws for Rational constants" $
        property (comparisonLaws :: Const Rational -> Const Rational -> Const Rational -> Property)
#if defined(CYCLOTOMIC)
      it "orders distinct real cyclotomic values without rounding" $ do
        let a = sqrt (IntegerC 2) :: Const Double
            b = a + RationalC (1/100000000000000000000)
        (a == b) `shouldBe` False
        (compare a b == EQ) `shouldBe` False
        forM_ (permutations [a, b]) $ \xs ->
          Set.size (Set.fromList xs) `shouldBe` 2
      it "preserves rational cyclotomic equivalences" $ do
        (RealCycC 2 :: Const Double) `shouldBe` RationalC 2
        (CycC 2 :: Const (Complex Double)) `shouldBe` RationalC 2
#endif
    describe "Default constant projection" $ do
      it "projects an evaluated value without numeric constraints" $
        fromConst (Const (WithDefaultConst True)) `shouldBe` WithDefaultConst True
      it "projects an exact integer" $
        (fromConst (IntegerC 123) :: WithDefaultConst Integer) `shouldBe` WithDefaultConst 123
      it "projects an exact rational" $
        (fromConst (RationalC (2/3)) :: WithDefaultConst Rational) `shouldBe` WithDefaultConst (2/3)
      it "projects a rational multiple of pi" $
        (fromConst (Pi (2/3)) :: WithDefaultConst Double) `shouldBe` WithDefaultConst ((2/3) * pi)
      it "projects Euler's number" $
        (fromConst E :: WithDefaultConst Double) `shouldBe` WithDefaultConst (exp 1)

#if defined(CYCLOTOMIC)
      it "projects a real cyclotomic value through the class default" $
        (fromConst (RealCycC (3/2)) :: WithDefaultConst Double) `shouldBe` WithDefaultConst (3/2)
      it "projects a complex cyclotomic value" $
        (fromConst (CycC (3/2)) :: Complex Double) `shouldBe` (3/2 :+ 0)

    describe "Real cyclotomic magnitude and sign" $ do
      it "preserves exact magnitudes and signs of rational values" $
        forM_ [-3/2, 0, 5/3] $ \q -> do
          let c = RealCycC (fromRational q) :: Const Double
          abs c `shouldBe` RationalC (abs q)
          signum c `shouldBe` RationalC (signum q)
          isExact (abs c) `shouldBe` True
          isExact (signum c) `shouldBe` True
      it "preserves exact magnitudes and signs of irrational radicals" $ do
        let root = sqrt (IntegerC 2) :: Const Double
        forM_ [-1, 1] $ \s -> do
          let c = IntegerC s * root
          abs c `shouldBe` root
          signum c `shouldBe` IntegerC s
          isExact (abs c) `shouldBe` True
          isExact (signum c) `shouldBe` True
      it "reports unsupported magnitudes without an approximate fallback" $ do
        let c = 1 + sqrt (IntegerC 2) :: Const Double
        evaluate (fromConst (abs c)) `shouldThrow` errorCall "abs not available for this number"
        evaluate (fromConst (signum c)) `shouldThrow` errorCall "signum not available for this number"
#endif
    it "Num operations over Integer correct" $
        property $ prop_num_equiv (Proxy :: Proxy Integer)
    it "Num operations over Rational correct" $
        property $ prop_num_equiv (Proxy :: Proxy Rational)
    it "Num operations over Float correct" $
        property $ prop_num_equiv (Proxy :: Proxy Float)
    it "Num operations over Double correct" $
        property $ prop_num_equiv (Proxy :: Proxy Double)

    describe "Exact integral operations" $ do
      it "quot preserves exactness and agrees with Integer" $
        property $ prop_integral_exact quot
      it "rem preserves exactness and agrees with Integer" $
        property $ prop_integral_exact rem
      it "div preserves exactness and agrees with Integer" $
        property $ prop_integral_exact div
      it "mod preserves exactness and agrees with Integer" $
        property $ prop_integral_exact mod

    it "Fractional operations over Rational correct" $
        property $ prop_frac_equiv (Proxy :: Proxy Rational)
    it "Fractional operations over Float correct" $
        property $ prop_frac_equiv (Proxy :: Proxy Float)
    it "Fractional operations over Double correct" $
        property $ prop_frac_equiv (Proxy :: Proxy Double)

    it "Unary Floating operations over Float correct" $
        property $ prop_float_equiv (Proxy :: Proxy Float)
    it "Unary Floating operations over Double correct" $
        property $ prop_float_equiv (Proxy :: Proxy Double)

    it "Binary Floating operations over Float correct" $
        property $ prop_float2_equiv (Proxy :: Proxy Float)
    it "Binary Floating operations over Double correct" $
        property $ prop_float2_equiv (Proxy :: Proxy Double)

comparisonLaws :: (Ord a, Show a) => a -> a -> a -> Property
comparisonLaws x y z = conjoin
  [ x === x
  , (x == y) === (y == x)
  , property (not (x == y && y == z) || x == z)
  , case compare x y of
      EQ -> x === y
      _  -> x =/= y
  , compare x y === invert (compare y x)
  , property (not (x <= y && y <= z) || x <= z)
  ]
  where
    invert LT = GT
    invert EQ = EQ
    invert GT = LT
