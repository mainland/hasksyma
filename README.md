# Hasksyma

[![Haskell CI](https://github.com/mainland/hasksyma/actions/workflows/haskell-ci.yml/badge.svg)](https://github.com/mainland/hasksyma/actions/workflows/haskell-ci.yml)

Hasksyma is a small computer algebra system embedded in Haskell. Its name is a
play on [Macsyma](https://en.wikipedia.org/wiki/Macsyma).

## Requirements

- GHC 9.10.3, 9.12.4, or 9.14.1
- cabal-install (3.16.1.0 in CI, 3.14.1.1 in the container)

All package components use GHC2024. GHCup is the recommended way to install
the Haskell toolchain.

## Documentation

The user guide is built with MkDocs and MathJax. To preview it locally:

```console
python3 -m venv .venv-docs
. .venv-docs/bin/activate
python -m pip install -r docs/requirements.txt
mkdocs serve
```

Use `mkdocs build --strict` to perform the same validation as CI and Read the
Docs. Generated files are written to `site/` and are not tracked.

See the [changelog](CHANGELOG.md) for notable changes and migration guidance.
The guide explains [simplification and domains](docs/getting-started.md#simplification-and-domains),
including when to use checked simplification to retain exclusions.

## Build and test

Build the reusable core library:

```console
cabal build hasksyma:lib:hasksyma
```

Run the test suite with partial evaluation enabled, which is the default:

```console
cabal test hasksyma:test:full --flags=+partial-evaluation --test-show-details=direct
```

The `partial-evaluation` flag remains supported and is tested in both states:

```console
cabal test hasksyma:test:full \
  --flags=-partial-evaluation \
  --test-show-details=direct
```

## IHaskell support

Notebook display support is isolated in the public `ihaskell` sublibrary and
enabled with the `ihaskell` flag. The flag is off by default so core builds can
resolve their dependencies without IHaskell or ZeroMQ. IHaskell 0.13 requires
GHC below 9.13, so use GHC 9.10.3 or 9.12.4 for notebook support. The
sublibrary is disabled on GHC 9.14.1. Build it with:

```console
cabal build hasksyma:lib:ihaskell --flags=+ihaskell
```

When depending on the sublibrary from another project, enable the flag in that
project's `cabal.project`:

```cabal
package hasksyma
  flags: +ihaskell
```

Importing the module activates the display instances:

```haskell
import Hasksyma.IHaskell ()
```

To install an IHaskell kernel, first install ZeroMQ and JupyterLab, then run:

```console
cabal install ihaskell-0.13.0.0 --overwrite-policy=always
ihaskell install
jupyter lab
```

On Debian or Ubuntu, the ZeroMQ development package is `libzmq3-dev`.

## Cyclotomic support

The optional `cyclotomic` flag requires constructors that are exposed by the
pinned custom fork. The Git dependency is deliberately confined to a separate
project file so ordinary builds use only released dependencies:

```console
cabal build \
  --project-file=cabal.project.cyclotomic \
  hasksyma:lib:hasksyma
```

The fork is pinned to commit
`edb448188d162c664f9b2ded65ebf4bb5ab7c88d`.

## Formatting and linting

Use Stylish Haskell 0.15.1.0 and HLint 3.10 for development:

```console
cabal install stylish-haskell-0.15.1.0 --overwrite-policy=always
cabal install hlint-3.10 --overwrite-policy=always
stylish-haskell -r -i src test ihaskell
hlint src test ihaskell
```

The checked-in VS Code settings select Stylish Haskell and format Haskell files on
every save. Install the recommended Haskell extension and ensure the pinned
`stylish-haskell` executable is on `PATH`.

## Container

The optional development image uses GHC 9.12.4 and installs IHaskell and
JupyterLab. Build it with your numeric user and group IDs, then mount this
checkout as the workspace:

```console
docker build \
  --build-arg USER_UID="$(id -u)" \
  --build-arg USER_GID="$(id -g)" \
  -t hasksyma:latest .

docker run --rm -it \
  -p 127.0.0.1:8888:8888 \
  -v "$PWD:/workspace" \
  hasksyma:latest
```
