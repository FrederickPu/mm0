#!/bin/sh
# Usage: ./run-mm0-lean.sh GROUP/TEST
# mm0-lean is the Lean .mm0 parser in mm0-lean4/ (`lake build mm0-lean`).
mm0-lean check ${1%.*}.mm0
