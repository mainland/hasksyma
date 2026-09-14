# Development

## Formatting and linting

The repository uses Stylish Haskell 0.15.1.0 and HLint 3.10:

```console
cabal install stylish-haskell-0.15.1.0 --overwrite-policy=always
cabal install hlint-3.10 --overwrite-policy=always
stylish-haskell -r -i src test ihaskell
hlint src test ihaskell
```

The checked-in VS Code settings run Stylish Haskell whenever a Haskell file is
saved.

## Continuous integration

The generated Haskell workflow tests the supported compilers. Together with
the additional checks, it covers both partial-evaluation modes, cyclotomic
constants, notebook support, formatting, lint, and documentation. Core, test, and notebook builds
must pass with warnings treated as errors in CI.

Regenerate the main workflow with the pinned tool after changing its settings:

```console
cabal install haskell-ci-0.19.20260901 --overwrite-policy=always
haskell-ci regenerate
```

Keep customizations in `.github/haskell-ci.patch`. Edit
`.github/workflows/additional-checks.yml` directly for the other jobs.

## Documentation

Create an isolated Python environment and install the pinned documentation
tools:

```console
python3 -m venv .venv-docs
. .venv-docs/bin/activate
python -m pip install -r docs/requirements.txt
```

Preview the guide while editing:

```console
mkdocs serve
```

Validate a production build:

```console
mkdocs build --strict
```

Inline mathematics uses `\(...\)` and display mathematics uses
`\[...\]`. PyMdown Arithmatex preserves the TeX source during Markdown
processing, and MathJax renders it in the browser.

API documentation is generated independently from Haddock comments:

```console
cabal haddock hasksyma:lib:hasksyma --haddock-all --disable-documentation
```

Examples introduced by `>>>` in Haddock comments are executable documentation.
CI checks them on GHC 9.12.4 with cabal-docspec 0.0.0.20250606, using the
checksum-pinned binary in `.github/workflows/haskell-ci.yml`. Each comment
group sees the documented module's public API, so explicitly import types or
constructors that the module does not export.

With the same cabal-docspec executable on `PATH`, build the core and run its
examples using the compiler selected for the Cabal build:

```console
cabal build hasksyma:lib:hasksyma
cabal-docspec hasksyma
```

If Cabal uses XDG directories, this cabal-docspec version needs their paths
explicitly. Set these variables before running it:

```console
export CABAL_CONFIG="$(cabal path --config-file)"
export CABAL_DIR="$(dirname "$(cabal path --store-dir)")"
```

## Container

Build the optional IHaskell development image with the current user's numeric
IDs:

```console
docker build \
  --build-arg USER_UID="$(id -u)" \
  --build-arg USER_GID="$(id -g)" \
  -t hasksyma:latest .
```

Start JupyterLab with the repository mounted as its workspace:

```console
docker run --rm -it \
  -p 127.0.0.1:8888:8888 \
  -v "$PWD:/workspace" \
  hasksyma:latest
```
