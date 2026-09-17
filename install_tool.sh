#!/bin/bash

# install_tool.sh — run once on the worker to build CORALean-C.
#
# Installs the Lean toolchain CORALean pins, fetches Mathlib's prebuilt oleans, and builds
# the `coralean-c` executable: Lean checks the copied CORALean modules (proofs included) and compiles the
# C it emits for every module the executable reaches, Mathlib's among them. Expect this to
# take a while; it happens once per worker.
#
# Argument:
# - $1: interface version string, e.g. "v1"

set -e

VERSION="${1:-v1}"
HERE="$(cd "$(dirname "$0")" && pwd)"
echo "Installing CORALean-C (interface $VERSION)"

# elan needs curl and git; a slim base image may ship neither.
if ! command -v curl >/dev/null || ! command -v git >/dev/null; then
    SUDO=""; [ "$(id -u)" -ne 0 ] && SUDO="sudo"
    $SUDO apt-get update -qq && $SUDO apt-get install -y -qq curl git ca-certificates
fi

if [ ! -x "$HOME/.elan/bin/lake" ]; then
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"

cd "$HERE"
lake exe cache get
lake build coralean-c

echo "built $(ls -l .lake/build/bin/coralean-c)"
nproc; free -g 2>/dev/null || true
