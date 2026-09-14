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
import           Control.Monad     (forM_)
import           Data.Complex      (Complex ((:+)))
import           Test.Hspec        (errorCall, shouldThrow)
#endif
import           Data.Proxy        (Proxy (Proxy))
import           Test.Hspec        (Spec, describe, it, shouldBe)
import           Test.QuickCheck

import           Hasksyma.Const
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
prop_frac_equiv _ (FracBinop _ f p) x y = p x y ==> fromConst (f x y) `equiv` f (fromConst x) (fromConst y)

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
prop_float_equiv _ (FloatUnop _ f p ) x = p x ==> fromConst (f x) `equiv` f (fromConst x)

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
prop_float2_equiv _ (FloatBinop _ f p) x y = p x y ==> fromConst (f x y) `equiv` f (fromConst x) (fromConst y)

constTests :: Spec
constTests = describe "Computations with constants" $ do
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
