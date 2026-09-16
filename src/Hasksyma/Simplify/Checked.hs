{-# LANGUAGE GADTs #-}

-- |
-- Module      :  Hasksyma.Simplify.Checked
-- Copyright   :  (c) 2026 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu
--
-- Mathematical simplification with retained source domains and replayable
-- derivations. Rules cancel identical differences and quotients. Traverse
-- supported children before their parents, visiting left children before right
-- children. Inputs
-- must belong to the real fragment supported by 'domainOf'. No traversal crosses
-- a calculus node or unsupported operation, and no legacy simplifier is called.
--
-- A result asserts equality under its recorded context, source domain, and
-- additional obligations. Its value is defined on that region. Extracting the
-- value alone discards these restrictions. In particular, cancelling @x / x@
-- produces one restricted to @x /= 0@, not an unrestricted constant function.
-- This mathematical claim does not assert identical floating-point evaluation.
-- Earlier partial evaluation during expression construction cannot be undone.
-- Results and derivations are public candidate data, not validity guarantees.
-- Local replay and external proof-assistant acceptance are separate checks.

module Hasksyma.Simplify.Checked
  ( Simplification (..),
    CheckError (..),
    Completion (..),
    Derivation (..),
    Step (..),
    Child (..),
    Rule (..),
    simplifyChecked,
    continueChecked,
    checkSimplification,
  ) where

import           Control.Applicative ((<|>))
import           Control.Monad       (guard)
import           Data.Foldable       (asum)
import           Data.Maybe          (isJust)

import           Hasksyma.Condition
import           Hasksyma.Const      (Const (IntegerC), IsConst)
import           Hasksyma.Exp        (Exp (..), FloatUnop (Cos, Sin), FracBinop (FDiv),
                                      NumBinop (Sub), sameExp)

-- | A rejected input, a known empty source domain, or an invalid request.
data CheckError
    = ConditionFailure ContextError -- ^ Unsupported mathematical input.
    | EmptySourceDomain             -- ^ The source domain is refuted in the context.
    | InvalidBudget                 -- ^ The rewrite budget is negative.
    | InvalidSimplification         -- ^ A continued result failed replay.
    deriving (Eq, Show)

-- | Search status, separate from validity of the completed derivation.
data Completion
    = NoApplicableRule -- ^ No implemented rule applies anywhere in the supported tree.
    | BudgetExhausted  -- ^ An applicable rule remains after the budget is consumed.
    deriving (Eq, Show)

-- | A candidate restricted value and its provenance. Public fields permit
-- construction, inspection, and record updates. Neither construction nor the
-- type itself establishes validity. Use 'checkSimplification' to replay the
-- claim against the intended source under 'contextUsed'. 'continueChecked'
-- replays the supplied claim before extending its derivation.
--
-- The derived 'Show' output uses record syntax and remains diagnostic, not a
-- serialization format.
data Simplification a = Simplification
    { contextUsed  :: Context a
      -- ^ The context in which the candidate claim is made.
    , original     :: Exp a
      -- ^ The original input, retained across continuations.
    , value        :: Exp a
      -- ^ The replacement. Using it alone discards the domain and obligations.
    , sourceDomain :: Condition a
      -- ^ The claimed exact original domain, including context-established exclusions.
    , obligations  :: Condition a
      -- ^ Additional sufficient requirements, separate from the source domain.
      -- These remain true in the initial checked engine.
    , derivation   :: Derivation a
      -- ^ The candidate chain from the original expression to the replacement.
    , completion   :: Completion
      -- ^ Search status. Replay does not verify this report.
    }
    deriving (Show)

-- | An ordered chain of candidate rule applications. Replay checks these
-- steps directly rather than rerunning simplification. An empty chain claims
-- that the original and replacement expressions are structurally identical.
-- 'Show' is diagnostic, not a certificate serialization format.
newtype Derivation a = Derivation [Step a]
    deriving (Show)

-- | A proposed local identity under the recorded real interpretation, source
-- domain, and obligations. A constructor names a rule, not evidence that its
-- application is valid. Replay checks the actual operands and result.
data Rule a
    = CancelDifference          -- ^ @u-u = 0@ for identical operands.
    | CancelQuotient            -- ^ @u/u = 1@ on the original quotient domain.
    deriving (Show)

-- | One edge in a path from the expression root to a local rewrite.
-- Paths use only supported unary and binary operations. A power's base is its
-- 'Operand'. No path crosses a calculus node or unsupported operation.
data Child
    = Operand      -- ^ The operand of a unary operation or the base of a power.
    | LeftOperand  -- ^ The left operand of a binary operation.
    | RightOperand -- ^ The right operand of a binary operation.
    deriving (Show)

-- | A candidate step: path from the root, local rule, whole expression before,
-- and whole expression after the rewrite. An empty path selects the root.
-- Replay checks the enclosing operators, parameters, and unaffected siblings
-- as well as the selected local identity.
data Step a = Step [Child] (Rule a) (Exp a) (Exp a)
    deriving (Show)

-- | Apply at most the supplied number of individual rewrites across the tree.
-- Child rewrites and parent rewrites consume the same budget. Restart the
-- traversal after each step so newly enabled rules are considered. The budget
-- bounds rule applications, not the work of inspecting the tree.
-- A zero budget returns the unchanged input with its domain and an appropriate
-- completion status.
-- Reject known empty domains even when no rewrite is requested. Unknown domain
-- satisfiability is allowed and does not establish that a valid input exists.
-- No additional hypotheses are introduced by this operation.
simplifyChecked :: (Eq a, IsConst a)
                => Int -> Context a -> Exp a -> Either CheckError (Simplification a)
simplifyChecked budget context expression
    | budget < 0 = Left InvalidBudget
    | otherwise = do
        domain <- conditionResult (domainOf context expression)
        requireDomain context domain
        pure (run budget (Simplification context expression expression domain
                          trueCondition (Derivation []) NoApplicableRule))

-- | Continue a checked result with an additional rewrite budget. Replay the
-- existing claim first and retain its context and full provenance. This never
-- recomputes the source domain from the replacement expression.
continueChecked :: (Eq a, IsConst a)
                => Int -> Simplification a -> Either CheckError (Simplification a)
continueChecked budget result
    | budget < 0 = Left InvalidBudget
    | not (checkSimplification (original result) result) = Left InvalidSimplification
    | otherwise = Right (run budget result)

conditionResult :: Either ContextError b -> Either CheckError b
conditionResult = either (Left . ConditionFailure) Right

requireDomain :: (Eq a, IsConst a) => Context a -> Condition a -> Either CheckError ()
requireDomain context domain = do
    decision <- conditionResult (decide context domain)
    case decision of
      Refuted _ -> Left EmptySourceDomain
      _         -> Right ()

run :: (Eq a, IsConst a) => Int -> Simplification a -> Simplification a
run budget (Simplification context source current domain hypotheses (Derivation steps) _) =
    case nextRewrite current of
      Nothing -> finish current steps NoApplicableRule
      Just (path, rule, next)
          | budget == 0 -> finish current steps BudgetExhausted
          | otherwise   -> run (budget - 1)
                               (finish next (steps ++ [Step path rule current next]) NoApplicableRule)
  where
    finish e proof = Simplification context source e domain hypotheses (Derivation proof)

nextRewrite :: (Eq a, IsConst a)
            => Exp a -> Maybe ([Child], Rule a, Exp a)
nextRewrite expression =
    asum (map rewriteChild [Operand, LeftOperand, RightOperand]) <|> rewriteHere
  where
    rewriteChild edge = do
        (child, rebuild) <- childAt edge expression
        (path, rule, next) <- nextRewrite child
        pure (edge : path, rule, rebuild next)

    rewriteHere = do
        (rule, next) <- nextRule expression
        pure ([], rule, next)

-- Only strict, extensional operations from the supported real fragment can
-- lift a child equality on the retained source domain. Rebuild with raw
-- constructors so partial evaluation cannot introduce unrecorded rewrites.
childAt :: Child -> Exp a -> Maybe (Exp a, Exp a -> Exp a)
childAt Operand (NumUnopE op x) = Just (x, NumUnopE op)
childAt Operand (FracUnopE op x) = Just (x, FracUnopE op)
childAt Operand (FloatUnopE op x)
    | op == Sin || op == Cos = Just (x, FloatUnopE op)
childAt Operand (NatPowE x n) = Just (x, (`NatPowE` n))
childAt Operand (IntPowE x n) = Just (x, (`IntPowE` n))
childAt LeftOperand (NumBinopE op x y) = Just (x, \z -> NumBinopE op z y)
childAt RightOperand (NumBinopE op x y) = Just (y, NumBinopE op x)
childAt LeftOperand (FracBinopE op x y) = Just (x, \z -> FracBinopE op z y)
childAt RightOperand (FracBinopE op x y) = Just (y, FracBinopE op x)
childAt _ _ = Nothing

focus :: [Child] -> Exp a -> Maybe (Exp a, Exp a -> Exp a)
focus [] expression = Just (expression, id)
focus (edge : path) expression = do
    (child, rebuild) <- childAt edge expression
    (selected, replace) <- focus path child
    pure (selected, rebuild . replace)

-- These rules require their operands to have values on the original domain.
-- Division and reciprocals supply nonzero requirements on that domain. Since
-- the domain is retained, no rule needs a new hypothesis or a sign test.
nextRule :: (Eq a, IsConst a) => Exp a -> Maybe (Rule a, Exp a)
nextRule (NumBinopE Sub x y)
    | sameExp x y = Just (CancelDifference, ConstE (IntegerC 0))
nextRule (FracBinopE FDiv x y)
    | sameExp x y = Just (CancelQuotient, ConstE (IntegerC 1))
nextRule _ = Nothing

-- | Replay a result against the intended original expression under the context
-- returned by 'contextUsed'. This does not rebind a proof to another context.
-- Check the exact domain and every rule's input, output, and position in the
-- chain. Obligations must be true for this initial rule set. Completion status
-- is a search report and is not used as evidence of mathematical validity.
-- This checks equality on the stated domain, not whether that domain is
-- inhabited. Known empty domains are rejected when starting simplification.
-- Public constructors and record updates may produce claims that fail replay.
-- A successful result is a local check under the recorded context, not Lean or
-- Rocq acceptance. The caller must also establish that this is the intended
-- context. This function binds only the supplied source, not a caller-supplied
-- context or independently specified conclusion.
checkSimplification :: (Eq a, IsConst a) => Exp a -> Simplification a -> Bool
checkSimplification expected (Simplification context source target domain hypotheses proof _) = isJust $ do
    guard (sameExp expected source)
    guard (checkDomain context source domain)
    case viewCondition hypotheses of
      TruthView True -> replay source proof
      _              -> Nothing
  where
    replay e (Derivation []) = guard (sameExp e target)
    replay e (Derivation (Step path rule before after : rest)) = do
        guard (sameExp e before)
        checkAt path rule before after
        replay after (Derivation rest)

checkAt :: (Eq a, IsConst a)
        => [Child] -> Rule a -> Exp a -> Exp a -> Maybe ()
checkAt path rule before after = do
    (x, rebuild) <- focus path before
    (y, _) <- focus path after
    guard (checkRule rule x y)
    guard (sameExp after (rebuild y))

-- Validate each rule directly. Do not trust rule discovery or merely compare
-- the final answers. These equations use mathematical real scalar semantics.
checkRule :: (Eq a, IsConst a) => Rule a -> Exp a -> Exp a -> Bool
checkRule CancelDifference (NumBinopE Sub x y) after =
    sameExp x y && sameExp after (ConstE (IntegerC 0))
checkRule CancelQuotient (FracBinopE FDiv x y) after =
    sameExp x y && sameExp after (ConstE (IntegerC 1))
checkRule _ _ _ = False
