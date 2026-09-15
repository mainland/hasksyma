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
