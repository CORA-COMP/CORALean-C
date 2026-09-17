#!/bin/bash

# run_instance.sh — run one instance and report the verdict.
#   args: v1 <benchmark> <instance> <params> [further catalog columns...] <results file>

set -u

VERSION_STRING="v1"
if [ "$1" != "$VERSION_STRING" ]; then
    echo "Expected first argument (version string) '$VERSION_STRING', got '$1'"
    exit 1
fi

HERE="$(cd "$(dirname "$0")" && pwd)"
# The results file is always the last argument.
exec "$HERE/.lake/build/bin/coralean-c" "$4" "${@: -1}"
