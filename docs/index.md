# Hasksyma

Hasksyma is a small computer algebra system embedded in Haskell. It represents
mathematical expressions as typed Haskell values and provides operations for
simplification, differentiation, heuristic integration, evaluation, and
pretty-printing.

For example, Hasksyma can construct and simplify the derivative

\[
\frac{d}{dx}\left(x^3 + 2x\right) = 3x^2 + 2.
\]

```haskell
{-# LANGUAGE OverloadedStrings #-}

import Hasksyma.Diff (diff)
import Hasksyma.Exp (Exp (VarE))
import Hasksyma.Simplify (simplify)

x :: Exp Double
x = VarE "x"

derivative :: Exp Double
derivative = simplify $ diff (x ^ (3 :: Integer) + 2 * x) x
```

Hasksyma deliberately exposes its expression constructors. This makes it
suitable for inspecting, transforming, and extending symbolic expressions from
ordinary Haskell code.

## Where to go next

- [Getting started](getting-started.md) explains how to build the library and
  create symbolic expressions.
- [Configuration](configuration.md) covers partial evaluation, cyclotomic
  constants, and IHaskell support.
- [Development](development.md) documents the contributor workflow.
