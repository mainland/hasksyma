{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- Module      :  Hasksyma.Simplify.Checked
-- Copyright   :  (c) 2026 Drexel University
-- License     :  BSD-style
-- Maintainer  :  mainland@drexel.edu
--
-- Mathematical simplification with retained source domains and replayable
-- derivations. Rules cancel identical differences and quotients, opposite
-- terms, zero products, and nested reciprocals, and reduce @sin(u)^2 + cos(u)^2@
-- to one. The trigonometric rule accepts natural and integer square constructors
-- in either term order and retains the domain of @u@. Traverse supported children
-- before their parents, visiting left children before right children. Inputs
-- must belong to the real fragment supported by 'domainOf'. No traversal crosses
-- a calculus node or unsupported operation, and no legacy simplifier is called.
--
-- Quotient rules cancel a matching factor on either side of a product and
-- reduce exact zero numerators. Retain all original denominator exclusions,
-- including those inside operands. No additional nonzero obligation is needed
-- on the original domain.
--
-- Checked simplification reduces @abs(u)@ to @u@ when 'decide' proves
-- 'nonNegative' @u@ in the recorded context. Explicit conditional simplification
-- can instead introduce that requirement when its truth is unknown. Replay
-- checks premise evidence or the introduction and subsequent reuse of an
-- obligation. Neither mode infers positivity from nonzero.
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
    simplifyConditional,
    continueConditional,
    checkSimplification,
  ) where

import           Control.Applicative        (Alternative (empty, (<|>)))
import           Control.Monad              (guard)
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.Reader (ReaderT, asks, runReaderT)
import           Data.Foldable              (asum)
import           Data.Maybe                 (isJust)

import           Hasksyma.Condition
import           Hasksyma.Const             (Const (IntegerC, Pi, RationalC), IsConst)
import           Hasksyma.Exp               (Exp (..), FloatUnop (Cos, Sin), FracBinop (FDiv),
                                             FracUnop (Recip), NumBinop (Add, Mul, Sub),
                                             NumUnop (Abs, Neg), sameExp)

-- | A rejected input, a known empty source domain, or an invalid request.
data CheckError
    = ConditionFailure ContextError -- ^ Unsupported mathematical input.
    | EmptySourceDomain             -- ^ The source domain is refuted in the context.
    | InvalidBudget                 -- ^ The rewrite budget is negative.
    | InvalidSimplification         -- ^ A continued result failed replay.
    deriving (Eq, Show)

-- | Search status in the requested mode, separate from derivation validity.
data Completion
    = NoApplicableRule -- ^ No rule permitted by the requested mode applies in the supported tree.
    | BudgetExhausted  -- ^ An applicable rule remains after the budget is consumed.
    deriving (Eq, Show)

-- | A candidate restricted value and its provenance. Public fields permit
-- construction, inspection, and record updates. Neither construction nor the
-- type itself establishes validity. Use 'checkSimplification' to replay the
-- claim against the intended source under 'contextUsed'. Both continuation
-- operations replay the supplied claim before extending its derivation.
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
      -- Fresh checked results have no additional requirements. Conditional
      -- rewriting can add requirements, which both continuations retain.
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
    | CancelOpposites           -- ^ @u+(-u) = 0@, in either term order.
    | ZeroProduct               -- ^ @0*u = 0@, in either factor order.
    | CancelReciprocals         -- ^ @recip (recip u) = u@ on the original domain.
    | PythagoreanIdentity       -- ^ @sin(u)^2 + cos(u)^2 = 1@, in either term order.
    | NonNegativeAbs (Evidence a) -- ^ @abs u = u@ with replayable nonnegativity evidence.
    | AssumeNonNegativeAbs      -- ^ @abs u = u@ while declaring a new nonnegativity obligation.
    | UseNonNegativeAbs         -- ^ @abs u = u@ using an earlier declared obligation.
    | ZeroQuotient              -- ^ @0/u = 0@ on the original quotient domain.
    | CancelProductNumerator    -- ^ Cancel either matching numerator factor.
    | CancelProductDenominator  -- ^ Cancel either matching denominator factor.
    deriving (Show)

data RewriteMode = PreserveDomain | AllowConditions
    deriving (Eq)

data RewriteEnv a = RewriteEnv
    { rewriteContext      :: Context a
    , rewriteMode         :: RewriteMode
    , rewriteRequirements :: [Exp a]
    }

-- Discovery reads a fixed environment and chooses the first successful
-- candidate. Only the driver records accepted steps and obligations, so failed
-- alternatives and budget probes cannot change the result's evidence.
newtype RewriteM a b = RewriteM (ReaderT (RewriteEnv a) Maybe b)
    deriving newtype (Functor, Applicative, Monad, Alternative)

runRewriteM :: RewriteEnv a -> RewriteM a b -> Maybe b
runRewriteM environment (RewriteM action) = runReaderT action environment

liftMaybe :: Maybe b -> RewriteM a b
liftMaybe = RewriteM . lift

askRewriteContext :: RewriteM a (Context a)
askRewriteContext = RewriteM (asks rewriteContext)

askRewriteMode :: RewriteM a RewriteMode
askRewriteMode = RewriteM (asks rewriteMode)

askRewriteRequirements :: RewriteM a [Exp a]
askRewriteRequirements = RewriteM (asks rewriteRequirements)

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
simplifyChecked = simplify PreserveDomain

-- | Simplify with permission to introduce additional sufficient obligations.
-- Currently, @abs(u)@ can become @u@ with a new 'nonNegative' @u@ obligation
-- when its sign is unknown. Proved premises need no new obligation, and refuted
-- premises leave the absolute value intact. The caller's context is unchanged.
-- The budget and input validation follow 'simplifyChecked'. A candidate found
-- after the budget is exhausted adds no obligation.
--
-- Obligations narrow the region covered by the result. They are not asserted
-- to hold throughout the source domain, to be jointly satisfiable, or to be
-- minimal. In particular, child rewrites can introduce obligations before a
-- parent cancellation that could have avoided them. Discharge these conditions
-- or retain them when using the replacement.
simplifyConditional :: (Eq a, IsConst a)
                    => Int -> Context a -> Exp a -> Either CheckError (Simplification a)
simplifyConditional = simplify AllowConditions

simplify :: (Eq a, IsConst a)
         => RewriteMode -> Int -> Context a -> Exp a -> Either CheckError (Simplification a)
simplify mode budget context expression
    | budget < 0 = Left InvalidBudget
    | otherwise = do
        domain <- conditionResult (domainOf context expression)
        requireDomain context domain
        pure (run mode budget (Simplification context expression expression domain
                          trueCondition (Derivation []) NoApplicableRule))

-- | Continue a checked result with an additional rewrite budget. Replay the
-- existing claim first and retain its context and full provenance. This never
-- recomputes the source domain from the replacement expression. Previously
-- introduced obligations may be reused, but no new obligations are added.
continueChecked :: (Eq a, IsConst a)
                => Int -> Simplification a -> Either CheckError (Simplification a)
continueChecked = continue PreserveDomain

-- | Continue with permission to introduce new obligations, retaining all prior
-- restrictions and replaying the existing claim first. Like 'simplifyConditional',
-- this may narrow coverage further. Existing nonnegativity obligations are
-- reused by structural operand identity, without a general assumptions solver.
continueConditional :: (Eq a, IsConst a)
                    => Int -> Simplification a -> Either CheckError (Simplification a)
continueConditional = continue AllowConditions

continue :: (Eq a, IsConst a)
         => RewriteMode -> Int -> Simplification a -> Either CheckError (Simplification a)
continue mode budget result
    | budget < 0 = Left InvalidBudget
    | not (checkSimplification (original result) result) = Left InvalidSimplification
    | otherwise = Right (run mode budget result)

conditionResult :: Either ContextError b -> Either CheckError b
conditionResult = either (Left . ConditionFailure) Right

requireDomain :: (Eq a, IsConst a) => Context a -> Condition a -> Either CheckError ()
requireDomain context domain = do
    decision <- conditionResult (decide context domain)
    case decision of
      Refuted _ -> Left EmptySourceDomain
      _         -> Right ()

run :: (Eq a, IsConst a) => RewriteMode -> Int -> Simplification a -> Simplification a
run mode budget (Simplification context source current domain _ (Derivation steps) _) =
    case runRewriteM environment (nextRewrite current) of
      Nothing -> finish current steps NoApplicableRule
      Just (path, rule, next)
          | budget == 0 -> finish current steps BudgetExhausted
          | otherwise   -> run mode (budget - 1)
                               (finish next (steps ++ [Step path rule current next]) NoApplicableRule)
  where
    environment = RewriteEnv context mode (concatMap requirements steps)

    finish e proof = Simplification context source e domain
        (allOf (map nonNegative (concatMap requirements proof))) (Derivation proof)

-- Only committed declaration steps contribute obligations. Continuation checks
-- their replay before using them, and replay checks each declaration's shape.
requirements :: Step a -> [Exp a]
requirements (Step path AssumeNonNegativeAbs before _)
    | Just (NumUnopE Abs x, _) <- focus path before = [x]
requirements _ = []

nextRewrite :: (Eq a, IsConst a)
            => Exp a -> RewriteM a ([Child], Rule a, Exp a)
nextRewrite expression =
    asum (map rewriteChild [Operand, LeftOperand, RightOperand]) <|> rewriteHere
  where
    rewriteChild edge = do
        (child, rebuild) <- liftMaybe (childAt edge expression)
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

-- Cancellation rules require their operands to have values on the original domain.
-- Division and reciprocals supply nonzero requirements on that domain. Since
-- the domain is retained, those rules need no new hypothesis or sign test.
-- Absolute-value removal records premise evidence or a scoped obligation.
nextRule :: (Eq a, IsConst a) => Exp a -> RewriteM a (Rule a, Exp a)
nextRule (NumBinopE Sub x y)
    | sameExp x y = pure (CancelDifference, ConstE (IntegerC 0))
nextRule (FracBinopE FDiv x y)
    | sameExp x y = pure (CancelQuotient, ConstE (IntegerC 1))
    | isExactZero x = pure (ZeroQuotient, ConstE (IntegerC 0))
nextRule (FracBinopE FDiv (NumBinopE Mul x y) z)
    | sameExp x z = pure (CancelProductNumerator, y)
    | sameExp y z = pure (CancelProductNumerator, x)
nextRule (FracBinopE FDiv z (NumBinopE Mul x y))
    | sameExp x z = pure (CancelProductDenominator, FracUnopE Recip y)
    | sameExp y z = pure (CancelProductDenominator, FracUnopE Recip x)
nextRule (NumBinopE Add x y)
    | opposites x y = pure (CancelOpposites, ConstE (IntegerC 0))
    | trigIdentity x y = pure (PythagoreanIdentity, ConstE (IntegerC 1))
nextRule (NumBinopE Mul x y)
    | isExactZero x || isExactZero y = pure (ZeroProduct, ConstE (IntegerC 0))
nextRule (FracUnopE Recip (FracUnopE Recip x)) = pure (CancelReciprocals, x)
nextRule (NumUnopE Abs x) = do
    context <- askRewriteContext
    case decide context (nonNegative x) of
      Right (Proved evidence) -> pure (NonNegativeAbs evidence, x)
      Right Unknown           -> useRequirement <|> introduceRequirement
      _                       -> empty
  where
    useRequirement = do
        required <- askRewriteRequirements
        guard (any (sameExp x) required)
        pure (UseNonNegativeAbs, x)

    introduceRequirement = do
        mode <- askRewriteMode
        guard (mode == AllowConditions)
        pure (AssumeNonNegativeAbs, x)
nextRule _ = empty

opposites :: (Eq a, IsConst a) => Exp a -> Exp a -> Bool
opposites x (NumUnopE Neg y) | sameExp x y = True
opposites (NumUnopE Neg x) y = sameExp x y
opposites _ _ = False

-- Only integral square syntax belongs to the supported interpretation. Match
-- arguments structurally without approximating constants or evaluating trig.
trigIdentity :: (Eq a, IsConst a) => Exp a -> Exp a -> Bool
trigIdentity x y = case (squareBase x, squareBase y) of
    (Just (FloatUnopE Sin u), Just (FloatUnopE Cos v)) -> sameExp u v
    (Just (FloatUnopE Cos u), Just (FloatUnopE Sin v)) -> sameExp u v
    _                                                  -> False

squareBase :: Exp a -> Maybe (Exp a)
squareBase (NatPowE x 2) = Just x
squareBase (IntPowE x 2) = Just x
squareBase _             = Nothing

-- Recognize only exact zero forms in the supported fragment, without evaluating
-- opaque payloads or deciding whether a compound expression is zero.
isExactZero :: Exp a -> Bool
isExactZero (ConstE (IntegerC 0))  = True
isExactZero (ConstE (RationalC 0)) = True
isExactZero (ConstE (Pi 0))        = True
isExactZero _                      = False

-- | Replay a result against the intended original expression under the context
-- returned by 'contextUsed'. This does not rebind a proof to another context.
-- Check the exact domain and every rule's input, output, and position in the
-- chain. Replay any premise evidence against the recorded context and its
-- actual claim without rerunning premise search. Replay obligation declarations
-- in order, allow reuse only after introduction, and check that the result's
-- obligations match the declarations exactly. This verifies a conditional
-- implication, not the truth of its obligations. Completion status is a search
-- report and is not used as evidence of mathematical validity.
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
    replay [] source proof
  where
    replay required e (Derivation []) = do
        guard (sameExp e target)
        guard (matchesRequirements required hypotheses)
    replay required e (Derivation (step@(Step path rule before after) : rest)) = do
        guard (sameExp e before)
        checkAt context required path rule before after
        replay (required ++ requirements step) after (Derivation rest)

-- Match precisely the normalized conjunction emitted by this rule set. Keep
-- declaration order and reject missing, extra, or differently shaped claims.
matchesRequirements :: (Eq a, IsConst a) => [Exp a] -> Condition a -> Bool
matchesRequirements [] condition = case viewCondition condition of
    TruthView True -> True
    _              -> False
matchesRequirements [x] condition = case viewCondition condition of
    NonNegativeView y -> sameExp x y
    _                 -> False
matchesRequirements xs condition = case viewCondition condition of
    ConjunctionView cs -> length xs == length cs && and (zipWith (matchesRequirements . pure) xs cs)
    _                  -> False

checkAt :: (Eq a, IsConst a)
        => Context a -> [Exp a] -> [Child] -> Rule a -> Exp a -> Exp a -> Maybe ()
checkAt context required path rule before after = do
    (x, rebuild) <- focus path before
    (y, _) <- focus path after
    guard (checkRule context required rule x y)
    guard (sameExp after (rebuild y))

-- Validate each rule directly. Do not trust rule discovery or merely compare
-- the final answers. These equations use mathematical real scalar semantics.
checkRule :: (Eq a, IsConst a) => Context a -> [Exp a] -> Rule a -> Exp a -> Exp a -> Bool
checkRule _ _ CancelDifference (NumBinopE Sub x y) after =
    sameExp x y && sameExp after (ConstE (IntegerC 0))
checkRule _ _ CancelQuotient (FracBinopE FDiv x y) after =
    sameExp x y && sameExp after (ConstE (IntegerC 1))
checkRule _ _ ZeroQuotient (FracBinopE FDiv x _) after =
    isExactZero x && sameExp after (ConstE (IntegerC 0))
checkRule _ _ CancelProductNumerator (FracBinopE FDiv (NumBinopE Mul x y) z) after =
    (sameExp x z && sameExp after y) || (sameExp y z && sameExp after x)
checkRule _ _ CancelProductDenominator (FracBinopE FDiv z (NumBinopE Mul x y)) after =
    (sameExp x z && sameExp after (FracUnopE Recip y)) ||
    (sameExp y z && sameExp after (FracUnopE Recip x))
checkRule _ _ CancelOpposites (NumBinopE Add x y) after =
    opposites x y && sameExp after (ConstE (IntegerC 0))
checkRule _ _ ZeroProduct (NumBinopE Mul x y) after =
    (isExactZero x || isExactZero y) && sameExp after (ConstE (IntegerC 0))
checkRule _ _ CancelReciprocals (FracUnopE Recip (FracUnopE Recip x)) after = sameExp after x
checkRule _ _ PythagoreanIdentity (NumBinopE Add x y) after =
    trigIdentity x y && sameExp after (ConstE (IntegerC 1))
checkRule context _ (NonNegativeAbs evidence) (NumUnopE Abs x) after =
    sameExp after x && checkDecision context (nonNegative x) (Proved evidence)
-- A declaration proves this local identity under its newly recorded premise.
-- Do not rediscover or assert the premise during replay.
checkRule _ _ AssumeNonNegativeAbs (NumUnopE Abs x) after = sameExp after x
checkRule _ required UseNonNegativeAbs (NumUnopE Abs x) after =
    sameExp after x && any (sameExp x) required
checkRule _ _ _ _ _ = False
