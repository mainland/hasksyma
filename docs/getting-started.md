# Getting started

## Requirements

Hasksyma supports GHC 9.10.3, 9.12.4, and 9.14.1 and uses GHC2024.
CI uses cabal-install 3.16.1.0, and the development container uses 3.14.1.1.
[GHCup](https://www.haskell.org/ghcup/) is the recommended way to install
the Haskell toolchain.

Build the core library from the repository root:

```console
cabal build hasksyma:lib:hasksyma
```

Run the full test suite:

```console
cabal test hasksyma:test:full --test-show-details=direct
```

## Create an expression

Start a REPL with the library in scope:

```console
cabal repl hasksyma:lib:hasksyma
```

The checked-in `.ghci` file provides startup settings and a pretty-printer.
These commands enable overloaded string literals explicitly and import the
complete public core API:

```haskell
:set -XOverloadedStrings

import Hasksyma

let x = VarE "x" :: Exp Double
```

For tighter control over names, import the individual modules instead.

The standard numeric classes construct symbolic syntax, so ordinary Haskell
operators can build expressions:

```haskell
let polynomial = x ^ (3 :: Integer) + 2 * x
let derivative = simplify $ diff polynomial x
```

Here `derivative` represents \(3x^2 + 2\).

Power constructors distinguish the type of the exponent:

| Constructor | Exponent | Base constraint |
| --- | --- | --- |
| `NatPowE` | `Natural` (nonnegative) | `Num a` |
| `IntPowE` | `Integer` (signed) | `Fractional a` |
| `FracPowE` | `Rational` (exact) | `Floating a`, `Floating (Const a)` |
| `FloatBinopE Pow` | `Exp a` (symbolic) | `Floating a`, `Floating (Const a)` |

For example, `NatPowE x 3`, `IntPowE x (-2)`, and `FracPowE x (1/2)`
represent a cube, an inverse square, and a rational power. Rational powers
use the underlying type's `(**)` semantics, including its behavior for
negative and complex bases. The matching `liftNatPow`, `liftIntPow`, and
`liftFracPow` helpers reduce constants when they can preserve exactness.

When migrating code that constructs expressions directly, replace the old
`IntPowE e n` with `NatPowE e (fromInteger n)` after checking that `n >= 0`.
Rename the old signed `FracPowE e n` to `IntPowE e n`. Likewise, rename the
old `liftIntPow` to `liftNatPow` and the old `liftFracPow` to `liftIntPow`.
The new `FracPowE` requires floating operations and cannot represent signed
powers over `Rational`. Derived `Show` and `Ord` results also change.

!!! note

    `diff` expects its second argument to be a `VarE` expression and reports an
    error otherwise. The expression constructors remain available when more
    direct control is required.

## Simplification and domains

Explicit `simplify` performs algebraic rewrites that can extend an expression's
domain. For example, `x/x` reduces to one, `0/x` to zero, and `(x*y)/x` or
`x*(y/x)` to `y`, including reversed factor orders. These results no longer
exclude `x = 0`. The result does not carry the original exclusions or a proof,
and simplification does not promise identical floating-point rounding,
overflow, or nonfinite evaluation. Matching factors use structural identity.

Division by a known zero still remains unreduced. Rules that combine different
powers or cancel nested inverses remain more conservative and require explicit
nonzero constants before removing the relevant exclusions.

The identity `sin u ^ 2 + cos u ^ 2 = 1` also remains conservative: cancellation
requires an explicit exact constant argument. Unknown arguments stay present,
although their subexpressions can still simplify. This restriction does not
guarantee identical floating-point evaluation for exact constants.

Opposite terms also cancel: `u-u`, `u+(-u)`, and `(-u)+u` reduce to zero when
the operands match structurally. For example, `recip x - recip x` simplifies
to zero without retaining the exclusion at `x = 0`. This algebraic policy also
permits cancellation of identical nonfinite payloads and exceptional leaves.

Multiplication by zero follows the same algebraic policy: `0 * recip x`
simplifies to zero without retaining the exclusion at `x = 0`. The same reduction
can occur when simplifying a derivative formula.

Construction and `evalexact` retain unknown quotients, opposite terms, and zero
products. This preserves the source syntax for callers that need to inspect its
domain before choosing a simplification operation.

## Mathematical contexts and conditions

`Hasksyma.Condition`, also re-exported by `Hasksyma`, provides explicit
mathematical contexts. Start with `emptyContext realScalars` and use `assuming`
to add hypotheses. The interpretation assigns mathematical real meanings to
supported expressions independently of their numerical carrier. It does not
change construction, numerical evaluation, or ordinary simplification.

Build propositions with `defined`, `nonZero`, `positive`, `nonNegative`, and
`allOf`. Query them with `decide`, which returns `Proved`, `Refuted`, or
`Unknown`. Unsupported syntax is a separate error. The checker handles exact
leaf facts, explicit assumptions, elementary implications such as positivity
implying nonzero, and structural definedness. It does not infer general signs
of compound expressions or establish that an accepted set of assumptions is
consistent.

Use `checkDecision` to replay evidence against a particular context and claim,
and `assumptionsUsed` to inspect its explicit dependencies. Use `viewCondition`
to inspect or render propositions without evaluating their expressions. These
checks are local rule checks, not external proof-assistant validation. See the
module's Haddock documentation for the supported syntax and interpretation.

Use `domainOf` to compute the exact definedness condition of a supported
expression. For example, the domain of `recip x` is `nonZero x`. Products by
zero and powers with exponent zero retain their operands' domain restrictions.
Context assumptions do not erase these restrictions from the returned condition.
Analysis sees the supplied expression and cannot recover syntax already removed
by construction or simplification.

`checkDomain` recomputes the normalized domain and compares it structurally with
a proposed condition. It can reject a logically equivalent condition with a
different representation. It also rejects merely sufficient conditions, such
as proposing `positive x` as the complete domain of `recip x`. Use `decide` to
check whether a domain holds under the current assumptions.

## Checked simplification and certificates

`simplifyChecked budget context expression` returns a restricted value with its
original source, context, exact source domain, and derivation. It cancels
identical differences and quotients, opposite terms, zero products, and nested
reciprocals throughout the supported real expression tree. For example,
cancelling `x/x` produces one while retaining `nonZero x` as its source domain.
The same exclusion remains when reducing `0 * recip x` to zero. Extracting
`value` alone loses that restriction.

Checked simplification also reduces `sin(u)^2 + cos(u)^2` to one in either
term order, with squares represented by `NatPowE` or `IntPowE`. The arguments
must match structurally. If `u` is `recip x`, the result retains `nonZero x`
as its source domain. This is a mathematical real identity and does not promise
identical floating-point evaluation.

To reduce `abs u` to `u`, checked simplification requires evidence that `u` is
nonnegative in the recorded context. An explicit nonnegative or positive
assumption can supply this evidence, as can an exact constant fact. Definedness
or nonzero alone does not establish the required sign. The result retains its
source domain and introduces no additional obligations. Replay checks the
stored evidence against the operand and the recorded context.

`simplifyConditional` uses the same engine but can reduce `abs u` when its sign
is unknown by recording `nonNegative u` in `obligations`. It keeps this new
requirement separate from the exact source domain and leaves the caller's
context unchanged. Proved premises need no new obligation, and refuted premises
leave the absolute value intact.

The result applies only where its source domain and obligations hold. These
obligations are sufficient requirements, not necessarily minimal or jointly
satisfiable. Child rewrites may add conditions before a parent cancellation
that could have avoided them. Discharge the obligations or retain them when
using the replacement.

The budget counts individual rewrites across the tree. Traversal visits children
before their parents and left children before right children. `completion`
reports whether a rule permitted by the requested mode remains applicable.
Use `continueChecked` to extend a result while retaining its original source
and restrictions. It can reuse previously declared obligations but adds none.
Use `continueConditional` to permit new obligations. Exhausting the budget
before a conditional step adds no obligation for that step.
Unsupported syntax and known empty source domains are rejected, including with
a zero budget. Unknown domain satisfiability is allowed.

`Simplification` is a public record. `Derivation`, `Step`, `Child`, and `Rule`
expose constructors for inspecting or building candidate certificates. A step
contains a path to the local rewrite, its rule, and the whole expression before
and after the step. The empty path selects the root. `Operand` selects a unary
operand or power base, and `LeftOperand` and `RightOperand` select binary operands.

Construction and record updates establish no validity. Use
`checkSimplification source result` to replay a candidate against the intended
source. Replay checks its source domain, rewrite chain, premise evidence,
enclosing operators, and unaffected operands. It checks obligation declarations
in order, permits reuse only after declaration, and requires the recorded
obligations to match those declarations. Both continuation functions replay the
supplied result before extending it and reject claims that fail replay.

Replay uses `contextUsed result`. The caller must establish that this is the
intended context and inspect the conclusion and restrictions. A successful local
check is separate from acceptance by Lean or another proof assistant. It does
not establish that the source domain is inhabited or that the obligations hold.
`completion` is a search report and is not checked by replay. Derived `Show`
output is diagnostic, not a certificate serialization format.
