#!/bin/bash
# Usage: LEAN=/path/to/lean MATHLIB_PACKAGES=/path/to/.lake/packages ./check_lean.sh CollatzElementary.lean
: "${LEAN:?set LEAN to the lean executable}"; : "${MATHLIB_PACKAGES:?set MATHLIB_PACKAGES}"
P="$MATHLIB_PACKAGES"
SEP=":"; case "$(uname -s)" in MINGW*|MSYS*|CYGWIN*) SEP=";";; esac
export LEAN_PATH="$P/mathlib/.lake/build/lib/lean$SEP$P/plausible/.lake/build/lib/lean$SEP$P/LeanSearchClient/.lake/build/lib/lean$SEP$P/importGraph/.lake/build/lib/lean$SEP$P/Qq/.lake/build/lib/lean$SEP$P/aesop/.lake/build/lib/lean$SEP$P/batteries/.lake/build/lib/lean$SEP$P/proofwidgets/.lake/build/lib/lean"
"$LEAN" "$@"; echo "lean exit code: $?"