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

!!! note

    `diff` expects its second argument to be a `VarE` expression and reports an
    error otherwise. The expression constructors remain available when more
    direct control is required.
