#!/bin/bash

# prepare_instance.sh — untimed setup before each instance.
#   args: v1 <benchmark> <instance> <params>
#
# Nothing to set up: the executable starts in milliseconds, and the inputs are generated
# by run_instance.sh as the catalog requires.

VERSION_STRING="v1"
if [ "$1" != "$VERSION_STRING" ]; then
    echo "Expected first argument (version string) '$VERSION_STRING', got '$1'"
    exit 1
fi
