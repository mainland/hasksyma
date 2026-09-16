{-# LANGUAGE GADTs #-}

-- |
-- Module      :  Hasksyma.Condition
-- Copyright   :  (c) 2026 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu
--
-- Explicit mathematical contexts, conditions, and elementary premise checking.
-- These operations do not change expression construction or numerical evaluation.
-- In particular, a mathematical real identity does not promise identical IEEE
-- rounding, overflow, or exceptional behavior when evaluated numerically.
--
-- The initial supported syntax comprises variables, exact integer and rational
-- constants, rational multiples of pi, Euler's number, ordinary arithmetic,
-- absolute value, signum, integral powers, sine, and cosine. 'Undefined', 'Infty',
-- and 'NegInfty' have no mathematical real value. Evaluated constant payloads,
-- cyclotomic constants, other floating operations, integral division operations,
-- and calculus nodes are currently unsupported. An assumption cannot make
-- unsupported syntax acquire a mathematical meaning.
--
-- Supported operations have strict mathematical partial-function semantics.
-- Operands must have values before an operation is applied. Integral powers
-- retain @0^0 = 1@, but an undefined base raised to zero is undefined. This
-- differs from some existing construction and simplification behavior. These
-- functions see only the expression supplied, including any earlier partial
-- evaluation performed while constructing it.
--
-- The checker recognizes facts about leaves, explicit assumptions, elementary
-- predicate implications, and structural definedness conditions. It does not
-- generally compute signs through compound expressions. Such queries can return
-- 'Unknown' even when a more capable checker could settle them. Conditions and
-- evidence are abstract, and their 'Show' output is diagnostic rather than a
-- serialization format.

module Hasksyma.Condition
  ( Interpretation,
    realScalars,
    Context,
    emptyContext,
    ContextError (..),
    assuming,
    Condition,
    ConditionView (..),
    viewCondition,
    defined,
    nonZero,
    positive,
    nonNegative,
    trueCondition,
    allOf,
    domainOf,
    checkDomain,
    Decision (..),
    Evidence,
    decide,
    checkDecision,
    assumptionsUsed,
  ) where

import           Data.List      (find, nubBy)

import           Hasksyma.Const (Const (..), IsConst)
import           Hasksyma.Exp   (Exp (..), FloatUnop (Cos, Sin), sameExp)

-- | The mathematical meaning assigned to supported expressions. Constructors
-- are private so additional interpretations can be introduced independently of
-- the numerical carrier of an expression.
data Interpretation = RealScalars
    deriving (Eq, Show)

-- | Mathematical real scalars. Variables range over finite real numbers.
-- Division requires a nonzero denominator. Integral powers use the
-- empty-product convention for a defined zero base raised to zero.
realScalars :: Interpretation
realScalars = RealScalars

-- | An interpretation and explicit hypotheses. Extending a context creates a
-- new value and does not change the scope of existing contexts or evidence.
data Context a = Context Interpretation [Condition a]
    deriving (Show)

-- | A context with no explicit hypotheses. Variable domains still follow from
-- the interpretation, so real variables are defined without an assumption.
emptyContext :: Interpretation -> Context a
emptyContext interpretation = Context interpretation []

-- | An unsupported mathematical input or an established contradiction.
data ContextError
    = UnsupportedConstant       -- ^ A constant has no supported interpretation.
    | UnsupportedOperation      -- ^ An operation has no supported interpretation.
    | ContradictoryAssumptions   -- ^ The proposed hypothesis is refuted.
    deriving (Eq, Show)

-- | A proposition interpreted in a context. Predicates on expressions without
-- a mathematical value are false, including nonzero and positivity predicates.
data Condition a
    = Boolean Bool
    | Atom Property (Exp a)
    | Conjunction [Condition a]
    deriving (Show)

data Property = IsDefined | IsNonZero | IsPositive | IsNonNegative
    deriving (Eq, Show)

-- | Public structure for inspecting and rendering a 'Condition'. Child
-- conditions can be inspected recursively with 'viewCondition'. Constructing
-- a view does not construct a condition or establish that a proposition holds.
-- Use the condition builders to construct propositions and 'decide' to query
-- them in a context.
data ConditionView a
    = TruthView Bool                 -- ^ A Boolean proposition.
    | DefinedView (Exp a)            -- ^ The expression has a value.
    | NonZeroView (Exp a)            -- ^ The expression has a nonzero value.
    | PositiveView (Exp a)           -- ^ The expression has a positive real value.
    | NonNegativeView (Exp a)        -- ^ The expression has a nonnegative real value.
    | ConjunctionView [Condition a]  -- ^ All child propositions hold.
    deriving (Show)

-- | Inspect one level of a condition without evaluating its expressions,
-- validating their interpretation, or deciding the proposition. This requires
-- no constraints on the numerical carrier. The view reflects the condition
-- after any normalization performed by its builder, not the original sequence
-- of builder calls. This is a structural interface, not a serialization format.
viewCondition :: Condition a -> ConditionView a
viewCondition (Boolean truth)          = TruthView truth
viewCondition (Atom IsDefined e)       = DefinedView e
viewCondition (Atom IsNonZero e)       = NonZeroView e
viewCondition (Atom IsPositive e)      = PositiveView e
viewCondition (Atom IsNonNegative e)   = NonNegativeView e
viewCondition (Conjunction conditions) = ConjunctionView conditions

-- | Assert that an expression denotes a value in the interpretation. For
-- 'realScalars', that value must be a finite mathematical real number.
defined :: Exp a -> Condition a
defined = Atom IsDefined

-- | Assert that an expression has a defined, nonzero value.
nonZero :: Exp a -> Condition a
nonZero = Atom IsNonZero

-- | Assert that an expression has a defined, strictly positive real value.
positive :: Exp a -> Condition a
positive = Atom IsPositive

-- | Assert that an expression has a defined, nonnegative real value.
nonNegative :: Exp a -> Condition a
nonNegative = Atom IsNonNegative

-- | The proposition true, requiring no hypotheses.
trueCondition :: Condition a
trueCondition = Boolean True

-- | Conjoin conditions. An empty conjunction is true. Flatten nested
-- conjunctions without evaluating expressions or dropping unsupported inputs.
allOf :: [Condition a] -> Condition a
allOf conditions = case concatMap conjuncts conditions of
    []  -> trueCondition
    [c] -> c
    cs  -> Conjunction cs

conjuncts :: Condition a -> [Condition a]
conjuncts (Boolean True)   = []
conjuncts (Conjunction cs) = concatMap conjuncts cs
conjuncts c                = [c]

-- | Compute the exact domain of a supported expression under the selected
-- interpretation. The resulting condition is equivalent to 'defined' of the
-- original expression. It retains nonzero denominator and negative-power
-- requirements, including in products by zero and powers with exponent zero.
--
-- Normalize intrinsic leaf facts and repeated conjuncts, without using context
-- hypotheses to erase restrictions. A false domain remains false. Validate all
-- input syntax before normalization, even when another operand has no value.
-- This is structural domain analysis, not general minimization of conditions.
domainOf :: (Eq a, IsConst a)
         => Context a -> Exp a -> Either ContextError (Condition a)
domainOf (Context RealScalars _) expression = do
    validateExpression expression
    realDomain expression

-- | Replay structural domain analysis and check a proposed normalized domain.
-- Equivalent conditions with different syntax may be rejected. This does not
-- decide general logical equivalence or prove a merely sufficient condition to
-- be the full domain.
checkDomain :: (Eq a, IsConst a)
            => Context a -> Exp a -> Condition a -> Bool
checkDomain context expression condition =
    validateCondition condition == Right () &&
    case domainOf context expression of
      Right expected -> sameCondition expected condition
      Left _         -> False

realDomain :: (Eq a, IsConst a) => Exp a -> Either ContextError (Condition a)
realDomain Undefined = pure (Boolean False)
realDomain Infty = pure (Boolean False)
realDomain NegInfty = pure (Boolean False)
realDomain VarE{} = pure trueCondition
realDomain (ConstE c) = case constantSign c of
    Just _  -> pure trueCondition
    Nothing -> Left UnsupportedConstant
realDomain (NumUnopE _ x) = realDomain x
realDomain (FracUnopE _ x) = nonzeroDomain x
realDomain (NumBinopE _ x y) =
    conjoinDomains <$> traverse realDomain [x, y]
realDomain (FracBinopE _ x y) = do
    dx <- realDomain x
    dy <- nonzeroDomain y
    pure (conjoinDomains [dx, dy])
realDomain (NatPowE x _) = realDomain x
realDomain (IntPowE x n)
    | n < 0     = nonzeroDomain x
    | otherwise = realDomain x
realDomain (FloatUnopE op x)
    | op == Sin || op == Cos = realDomain x
realDomain _ = Left UnsupportedOperation

nonzeroDomain :: (Eq a, IsConst a) => Exp a -> Either ContextError (Condition a)
nonzeroDomain expression = do
    domain <- realDomain expression
    let condition = nonZero expression
    pure (conjoinDomains [domain, maybe condition Boolean (elementary condition)])

-- Inputs have already been validated, so absorbing false cannot hide an
-- unsupported expression. Keep this separate from the public conjunction builder.
conjoinDomains :: (Eq a, IsConst a) => [Condition a] -> Condition a
conjoinDomains conditions
    | any isFalse flattened = Boolean False
    | otherwise             = allOf (nubBy sameCondition flattened)
  where
    flattened = concatMap conjuncts conditions

    isFalse (Boolean False) = True
    isFalse _               = False

-- | A proved proposition, a proved negation of that proposition, or an
-- unsettled query. Refuting positivity does not prove negativity, since zero
-- and undefined expressions also fail the positivity predicate.
data Decision a
    = Proved (Evidence a)
    | Refuted (Evidence a)
    | Unknown
    deriving (Show)

-- | Replayable evidence bound to an interpretation, conclusion, polarity, and
-- its used hypotheses. Constructors are private. Use 'checkDecision' to replay
-- a decision against the intended context and proposition.
data Evidence a = Evidence Interpretation (Condition a) Bool (Reason a)
    deriving (Show)

data Reason a
    = Elementary
    | Hypothesis (Condition a)
    | AllProved [Evidence a]
    | OneRefuted Int (Evidence a)
    | DefinedOn (Evidence a)
    | UndefinedValue (Evidence a)
    deriving (Show)

-- | Add a hypothesis after validating its syntax and checking for a known
-- contradiction. An unknown supported proposition may be assumed. Acceptance
-- does not prove the hypothesis true or establish general context consistency.
-- Evidence from this context records any hypotheses it uses.
assuming :: (Eq a, IsConst a)
         => Condition a -> Context a -> Either ContextError (Context a)
assuming condition context@(Context interpretation hypotheses) = do
    decision <- decide context condition
    case decision of
      Refuted _ -> Left ContradictoryAssumptions
      _         -> Right (Context interpretation (hypotheses ++ conjuncts condition))

-- | Decide a proposition using exact leaf facts, explicit hypotheses, and
-- elementary implications. Positivity implies nonnegativity, nonzero, and
-- definedness. Nonnegativity and nonzero each imply definedness.
-- Definedness follows from the exact structural domain. An established lack
-- of a value also refutes nonzero, positivity, and nonnegativity.
--
-- Validate the entire condition before inference, including all conjuncts.
-- Unsupported syntax is an error, distinct from 'Unknown'. Neither numerical
-- evaluation nor the ordinary expression simplifier participates in checking.
decide :: (Eq a, IsConst a)
       => Context a -> Condition a -> Either ContextError (Decision a)
decide context condition = do
    validateCondition condition
    pure (infer context condition)

-- A definedness query reduces to predicates on strict subexpressions. A sign
-- query may first check definedness of the same expression, but that check
-- never asks for its sign again. No fixed-point proof search is needed.
infer :: (Eq a, IsConst a) => Context a -> Condition a -> Decision a
infer context@(Context interpretation hypotheses) condition
    | Just truth <- elementary condition = result truth Elementary
    | Just hypothesis <- find (`implies` condition) hypotheses =
        result True (Hypothesis hypothesis)
    | Conjunction cs <- condition =
        let decisions = map (infer context) cs
        in case [(i, evidence) | (i, Refuted evidence) <- zip [0..] decisions] of
             (i, evidence) : _ -> result False (OneRefuted i evidence)
             [] -> case traverse proved decisions of
                     Just evidence -> result True (AllProved evidence)
                     Nothing       -> Unknown
    | Atom IsDefined expression <- condition =
        case domainOf context expression of
          Right domain -> case infer context domain of
              Proved evidence  -> result True (DefinedOn evidence)
              Refuted evidence -> result False (DefinedOn evidence)
              Unknown          -> Unknown
          Left _ -> Unknown
    | Atom p expression <- condition, needsDefinedValue p =
        case infer context (defined expression) of
          Refuted evidence -> result False (UndefinedValue evidence)
          _                -> Unknown
    | otherwise = Unknown
  where
    result truth reason
        | truth     = Proved evidence
        | otherwise = Refuted evidence
      where
        evidence = Evidence interpretation condition truth reason

    proved (Proved evidence) = Just evidence
    proved _                 = Nothing

-- | Replay evidence against a requested proposition and context. Reject
-- changed conclusions, reversed decision polarity, and missing used hypotheses.
-- Additional unrelated hypotheses are permitted. 'Unknown' returns false
-- because it supplies no evidence to check.
--
-- This checks rule evidence directly, without running the premise search.
checkDecision :: (Eq a, IsConst a)
              => Context a -> Condition a -> Decision a -> Bool
checkDecision context condition (Proved evidence) =
    checkEvidence context condition True evidence
checkDecision context condition (Refuted evidence) =
    checkEvidence context condition False evidence
checkDecision _ _ Unknown = False

checkEvidence :: (Eq a, IsConst a)
              => Context a -> Condition a -> Bool -> Evidence a -> Bool
checkEvidence context@(Context interpretation hypotheses) condition truth
              (Evidence interpretation' conclusion truth' reason) =
    interpretation == interpretation' &&
    sameCondition condition conclusion && truth == truth' &&
    validateCondition condition == Right () &&
    case reason of
      Elementary -> elementary condition == Just truth
      Hypothesis hypothesis ->
          truth && any (sameCondition hypothesis) hypotheses &&
          hypothesis `implies` condition
      AllProved evidence -> case condition of
          Conjunction cs -> truth && length cs == length evidence &&
                            and (zipWith (\c -> checkEvidence context c True) cs evidence)
          _              -> False
      OneRefuted i evidence -> case condition of
          Conjunction cs | not truth, i >= 0 -> case drop i cs of
              c : _ -> checkEvidence context c False evidence
              []    -> False
          _ -> False
      DefinedOn evidence -> case condition of
          Atom IsDefined expression -> case domainOf context expression of
              Right domain -> checkEvidence context domain truth evidence
              Left _       -> False
          _ -> False
      UndefinedValue evidence -> case condition of
          Atom p expression | not truth, needsDefinedValue p ->
              checkEvidence context (defined expression) False evidence
          _ -> False

-- | The explicit hypotheses referenced by evidence, possibly with duplicates.
-- Facts established directly from the interpretation require no hypotheses.
-- Replay requires these propositions to remain available in the context.
assumptionsUsed :: Evidence a -> [Condition a]
assumptionsUsed (Evidence _ _ _ reason) = case reason of
    Elementary              -> []
    Hypothesis hypothesis   -> [hypothesis]
    AllProved evidence      -> concatMap assumptionsUsed evidence
    OneRefuted _ evidence   -> assumptionsUsed evidence
    DefinedOn evidence      -> assumptionsUsed evidence
    UndefinedValue evidence -> assumptionsUsed evidence

implies :: (Eq a, IsConst a) => Condition a -> Condition a -> Bool
implies (Atom p x) (Atom q y) = sameExp x y && propertyImplies p q
implies p q                   = sameCondition p q

-- Enumerate implications so adding a predicate does not silently give it laws.
propertyImplies :: Property -> Property -> Bool
propertyImplies p q | p == q = True
propertyImplies IsPositive    IsNonNegative = True
propertyImplies IsPositive    IsNonZero     = True
propertyImplies IsPositive    IsDefined     = True
propertyImplies IsNonNegative IsDefined     = True
propertyImplies IsNonZero     IsDefined     = True
propertyImplies _             _             = False

-- Definedness has its own rule. Enumerate the other predicates whose truth
-- requires a value, rather than giving every future predicate this premise.
needsDefinedValue :: Property -> Bool
needsDefinedValue p = p `elem` [IsNonZero, IsPositive, IsNonNegative]

sameCondition :: (Eq a, IsConst a) => Condition a -> Condition a -> Bool
sameCondition (Boolean x) (Boolean y) = x == y
sameCondition (Atom p x) (Atom q y) = p == q && sameExp x y
sameCondition (Conjunction xs) (Conjunction ys) =
    length xs == length ys && and (zipWith sameCondition xs ys)
sameCondition _ _ = False

elementary :: Condition a -> Maybe Bool
elementary (Boolean truth)         = Just truth
elementary (Atom IsDefined VarE{}) = Just True
elementary (Atom p (ConstE c))     = signFact p <$> constantSign c
elementary (Atom _ Undefined)      = Just False
elementary (Atom _ Infty)          = Just False
elementary (Atom _ NegInfty)       = Just False
elementary _                       = Nothing

constantSign :: Const a -> Maybe Ordering
constantSign (IntegerC n)  = Just (compare n 0)
constantSign (RationalC q) = Just (compare q 0)
constantSign (Pi q)        = Just (compare q 0)
constantSign E             = Just GT
constantSign _             = Nothing

signFact :: Property -> Ordering -> Bool
signFact IsDefined     _    = True
signFact IsNonZero     sign = sign /= EQ
signFact IsPositive    sign = sign == GT
signFact IsNonNegative sign = sign /= LT

validateCondition :: Condition a -> Either ContextError ()
validateCondition (Boolean _)      = Right ()
validateCondition (Atom _ e)       = validateExpression e
validateCondition (Conjunction cs) = mapM_ validateCondition cs

validateExpression :: Exp a -> Either ContextError ()
validateExpression Undefined = Right ()
validateExpression Infty = Right ()
validateExpression NegInfty = Right ()
validateExpression VarE{} = Right ()
validateExpression (ConstE c) = case constantSign c of
    Just _  -> Right ()
    Nothing -> Left UnsupportedConstant
validateExpression (NumUnopE _ x) = validateExpression x
validateExpression (FracUnopE _ x) = validateExpression x
validateExpression (NumBinopE _ x y) = validateExpression x >> validateExpression y
validateExpression (FracBinopE _ x y) = validateExpression x >> validateExpression y
validateExpression (NatPowE x _) = validateExpression x
validateExpression (IntPowE x _) = validateExpression x
validateExpression (FloatUnopE op x)
    | op == Sin || op == Cos = validateExpression x
validateExpression _ = Left UnsupportedOperation
