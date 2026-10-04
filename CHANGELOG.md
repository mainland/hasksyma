# Revision history for Hasksyma

## Unreleased

### API and compatibility

- Require GHC 9.10 or later and use GHC2024. Declare GHC 9.10.3, 9.12.4,
  and 9.14.1 in `tested-with`.
- Re-export the public core API from `Hasksyma` and define explicit module
  export lists. Move notebook display instances to `Hasksyma.IHaskell` in the
  optional public `hasksyma:ihaskell` sublibrary. Enable the `ihaskell` flag
  and import that module to use these instances. Notebook support requires
  GHC below 9.13 with the current IHaskell dependency. QuickCheck instances
  are test-only, so downstream tests must supply their own generators.
- Name power constructors by exponent type. `NatPowE` takes `Natural`,
  `IntPowE` takes `Integer`, and the new `FracPowE` takes `Rational`.
  Migrate the former `IntPowE` and `FracPowE` constructors to `NatPowE` and
  `IntPowE`, respectively. Use the matching `liftNatPow`, `liftIntPow`, and
  `liftFracPow` helpers. General symbolic exponents still use `FloatBinopE Pow`.
- Interpret `Root` operands as degree first and radicand second. Swap operands
  in existing `Root` expressions and calls to `floatbinop Root` or
  `liftFloating2 Root` to preserve their previous evaluated meaning. Text
  output uses `x ** recip n` with either partial-evaluation setting.
- Compare constants using exact keys rather than rounded numerical values.
  `IsConst.exactRational` lets finite floating payloads participate through
  their exact binary rational values. Custom payloads default to opaque
  comparison. Ordering of constants and expressions is structural. Use
  `fromConst` for numerical comparison. Floating NaNs remain nonreflexive.
- Add `sameConst`, `sameExp`, and `IsConst.samePayload` for structural rewrite
  identity. These preserve constant representations, distinguish signed zeros,
  and recognize unchanged Float, Double, and complex NaNs without changing
  algebraic equality.
- Apply `mapExp` callbacks to leaves as well as compound expressions. Existing
  callbacks must handle variables, constants, and exceptional leaves. Traversal
  is bottom-up, leaves calculus variable fields alone, and does not traverse
  syntax introduced by the callback during the same pass.
- Add `rewriteWithLimit`, `simplifyWithLimit`, and `RewriteResult` to report
  fixed points, cycles, and exhausted budgets. `simplifyn` treats nonpositive
  budgets as zero work and stops on detected cycles. Unbounded rewriting still
  requires terminating rules and suitable payload identity.
- Add `toRationalMaybe` and `toIntegerMaybe` for constant projections without
  approximation. Partial numeric conversions support exact zero multiples of
  pi and rational cyclotomic values, and report descriptive errors for
  unsupported symbolic conversions. Payload conversions retain their native
  behavior.

### Mathematical contexts and checked simplification

- Add `Hasksyma.Condition` with explicit mathematical real contexts,
  assumptions, inspectable conditions, exact structural source domains, and
  elementary premise checking. Distinguish unsupported syntax from unknown
  facts. Replay evidence against its claim and context, and expose the
  assumptions it uses. Definedness is strict, including for zero products and
  zero powers. The supported fragment includes integers, rationals, rational multiples of
  pi, Euler's number, arithmetic, integral powers, absolute value, signum, sine,
  and cosine. Evaluated payloads, cyclotomic constants, fractional powers,
  logarithms, and calculus nodes remain unsupported.
- Add `Hasksyma.Simplify.Checked` with bounded traversal and continuation.
  Results retain the original expression, context, exact source domain,
  obligations, completion status, and derivation. Rules include cancellation,
  zero products and numerators, nested reciprocals, matching quotient factors,
  integral-power products, quotients and nesting, and the Pythagorean identity.
  Absolute-value removal uses proved nonnegativity. Natural-only power laws
  retain `Num` constraints, and exponent subtraction uses signed arithmetic.
- Use the same engine for `simplifyChecked` and `simplifyConditional`.
  Conditional simplification may remove an absolute value by recording a new
  nonnegativity obligation. Source restrictions and caller assumptions remain
  separate from these obligations. Checked continuation preserves existing
  obligations without introducing new ones.
- Expose the `Simplification` record and certificate constructors for inspection
  and construction. `checkSimplification` checks the requested source, recorded
  context, exact domain, rule applications, traversal paths, and obligation
  introduction and reuse. Certificates are candidate claims, not validity
  guarantees. Local replay is separate from external proof-assistant acceptance.
  Extracting only the result's value discards its restrictions. These operations
  express mathematical real identities, not identical floating-point evaluation.

### Evaluation, simplification, and integration

- Preserve negative fractional signs in LaTeX output, including complex
  imaginary components.
- Avoid overflow when rendering the minimum `Int` as LaTeX.
- Render floating infinities explicitly in LaTeX and handle NaNs before
  integral conversion.
- Preserve exact rational coefficients and symbolic irrational constants during
  factorization and heuristic integration. Factor lists retain irrational
  constants as bases, and rational coefficients may use `RationalC`.
- Decompose raw reciprocals consistently with negative integer powers in both
  partial-evaluation modes.
- Keep known-zero divisors unreduced in exact integral evaluation. Ordinary
  evaluation retains the underlying division-by-zero exception.
- Stop ordinary simplification from cycling on products of powers with
  constant bases. Such powers no longer move ahead of every product or
  quotient factor, so some products keep their original factor order.
- Document ordinary simplification as algebraic rewriting that may extend the
  source domain. It cancels matching opposite terms and quotient factors and
  reduces zero products and numerators without recording exclusions. Known-zero
  division stays unreduced. Construction and `evalexact` retain unknown zero
  products, opposite terms, and quotients. Use checked simplification when
  supported rewrites must retain source restrictions and derivations.
- Guard domain-sensitive power and logarithm rewrites. General floating-power
  combination requires explicit positive exact bases. Cancellation of nested
  reciprocals, quotients of different powers, and elimination of negative
  exponents require explicit nonzero exact bases. Exponential/logarithm
  cancellation uses established positive exact arguments and rational exponents
  where required. `logBase` identities exclude base one. Logarithm sums and
  differences are no longer combined without branch conditions. Ordinary
  trigonometric identity cancellation requires an explicit exact argument.
  Simplified output may retain operations that previously disappeared.
- Preserve exact constants during integral folding and simplifier negation,
  including symbolic Euler's number. Interpret every constant constructor in
  the default `IsConst` instance, preserve signed powers of symbolic bases,
  and guard exact integer logarithm recognition against invalid estimates.
- Recognize perfect integer squares using integer arithmetic, including large
  values and cyclotomic configurations. Negative real square roots stay
  unreduced during exact evaluation and use floating semantics during numerical
  evaluation. Preserve principal complex square roots.
- Evaluate division by exact zero, reciprocals, and negative powers of zero
  using the underlying numeric type. Floating payloads can produce infinities
  or NaNs, while rational payloads retain their division-by-zero exception.
  Exact evaluation and simplification leave known-zero division unreduced.
  Integral powers consistently use `0^0 = 1`.
- Keep fractional and non-integer general powers intact during factorization.
  Their factor lists now contain whole powers with integer multiplicities.
  Recognize these intact factors during heuristic integration to retain
  power-rule and derivative-divides substitution coverage. Correct extracted
  factor signs and preserve reciprocal factors for empty numerator lists.
- Correct `fvs` and `freeOf` for integrals. Definite integrals bind their
  variable only in the integrand. Indefinite integrals retain that dependency,
  including for constant integrands.
- Omit known-zero derivative terms under the local differentiability contract.
  Leave the derivative of `log (abs u)` unresolved without real-domain evidence.
  Reciprocal integration uses `log (u^2)/2` with the substitution coefficient,
  and tangent integration uses `-log (cos x ^ 2)/2`. These expressions give
  local primitives on appropriate real intervals or complex regions away
  from zeros and logarithm branch cuts.
- Fix exact real cyclotomic `abs` and `signum` when the squared magnitude is
  rational. Other squared magnitudes remain unsupported without approximation.

### Development and distribution

- Replace Stack with Cabal workflows and move core sources under `src/`.
  Isolate notebook dependencies and keep cyclotomic support in a separately
  pinned project file. Retain both partial-evaluation configurations.
- Add warning checks, Stylish Haskell and HLint configuration, Haddock examples,
  a MkDocs guide, and CI for supported compilers and optional configurations.
  Repair numerical test helpers so unknown values and exceptional results do
  not silently pass comparisons.
- Correct relative-error comparisons of negative values and explicitly compare
  zeros, NaNs, and signed infinities. Add regressions for these comparison
  policies.
- Normalize the package version to `0.1.0.0`, add the issue tracker URL, and
  include this changelog, the guide, and supporting development files in source
  distributions.
