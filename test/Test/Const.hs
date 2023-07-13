{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- |
-- Module      :  Test.Const
-- Copyright   :  (c) 2023 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu

module Test.Const where

import Data.Proxy ( Proxy(Proxy) )
import Test.Hspec ( describe, it, Spec )
import Test.QuickCheck

import Hasksyma.Const

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

data FracBinop = FracBinop String (forall a . Fractional a => a -> a -> a) (forall a . (Eq a, Fractional a) => a -> a -> Bool)

instance Show FracBinop where
    show (FracBinop op _ _) = op

instance Arbitrary FracBinop where
    arbitrary = elements [FracBinop "(/)" (/) (\_ y -> y /= 0)]

prop_frac_equiv :: (IsConst a, Fractional a, Equiv a)
                => proxy a
                -> FracBinop -> Const a -> Const a -> Property
prop_frac_equiv _ (FracBinop _ f p) x y = p x y ==> fromConst (f x y) `equiv` f (fromConst x) (fromConst y)

data FloatUnop = FloatUnop String (forall a . Floating a => a -> a)

instance Show FloatUnop where
    show (FloatUnop op _) = op

instance Arbitrary FloatUnop where
    arbitrary = elements [ FloatUnop "exp" exp
                         , FloatUnop "log" log
                         , FloatUnop "sqrt" sqrt
                         , FloatUnop "sin" sin
                         , FloatUnop "cos" cos
                         , FloatUnop "tan" tan
                         , FloatUnop "asin" asin
                         , FloatUnop "acos" acos
                         , FloatUnop "atan" atan
                         , FloatUnop "sinh" sinh
                         , FloatUnop "cosh" cosh
                         , FloatUnop "tanh" tanh
                         , FloatUnop "asinh" asinh
                         , FloatUnop "acosh" acosh
                         , FloatUnop "atanh" atanh
                         ]

prop_float_equiv :: (IsConst a, Floating a, Equiv a, Floating (Const a))
                 => proxy a
                 -> FloatUnop -> Const a -> Property
prop_float_equiv _ (FloatUnop _ f) x = fromConst (f x) `equiv` f (fromConst x)

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
    it "Num operations over Integer correct" $
        property $ prop_num_equiv (Proxy :: Proxy Integer)
    it "Num operations over Rational correct" $
        property $ prop_num_equiv (Proxy :: Proxy Rational)
    it "Num operations over Float correct" $
        property $ prop_num_equiv (Proxy :: Proxy Float)
    it "Num operations over Double correct" $
        property $ prop_num_equiv (Proxy :: Proxy Double)

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
