#!/bin/sh
set -e

cabal test hasksyma:test:full --test-show-details=direct "$@"
