# Configuration

Hasksyma keeps optional behavior behind Cabal flags and components so the core
library does not acquire unnecessary dependencies.

## Partial evaluation

The `partial-evaluation` flag is enabled by default. It allows the numeric
instances for `Exp` to simplify elementary identities and constant operations
while expressions are constructed.

Test the alternative representation-preserving behavior with:

```console
cabal test hasksyma:test:full \
  --flags=-partial-evaluation \
  --test-show-details=direct
```

Both flag states are covered by continuous integration.

## Cyclotomic constants

The optional `cyclotomic` flag enables exact cyclotomic constants. Hasksyma
requires constructors exposed by a custom `cyclotomic` fork, so the dependency
is isolated in `cabal.project.cyclotomic` and pinned to a specific commit.

```console
cabal build \
  --project-file=cabal.project.cyclotomic \
  hasksyma:lib:hasksyma
```

Ordinary builds continue to use released Hackage dependencies only.

## IHaskell

Notebook display instances live in the public `ihaskell` sublibrary. Enable it
with the `ihaskell` flag, which is off by default so core builds can resolve
without IHaskell or ZeroMQ. Use GHC 9.10.3 or 9.12.4 for notebook support.
The sublibrary is disabled on GHC 9.14.1 because IHaskell 0.13 requires GHC
below 9.13. Build it with:

```console
cabal build hasksyma:lib:ihaskell --flags=+ihaskell
```

When using the sublibrary from another project, enable the flag in that
project's `cabal.project`:

```cabal
package hasksyma
  flags: +ihaskell
```

Importing the integration module activates the display instances:

```haskell
import Hasksyma.IHaskell ()
```

To run notebooks, install ZeroMQ and JupyterLab, then install and register an
IHaskell kernel:

```console
cabal install ihaskell-0.13.0.0 --overwrite-policy=always
ihaskell install
jupyter lab
```

The repository's `Dockerfile` provides the same environment in a container.
