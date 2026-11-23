#!/bin/bash
# Builds every Lean module of this directory in dependency order (oleans in ./build) and prints exit code, warning count and sorry mentions.
# Usage: LEAN=/path/to/lean MATHLIB_PACKAGES=/path/to/.lake/packages ./build_all.sh          (Lean 4.35.0 with the Mathlib oleans of that version)
# Single module (earlier modules must be built first): LEAN=... MATHLIB_PACKAGES=... ./build_all.sh CollatzCrossing
: "${LEAN:?set LEAN to the lean executable}"; : "${MATHLIB_PACKAGES:?set MATHLIB_PACKAGES to the .lake/packages directory}"
P="$MATHLIB_PACKAGES"
SEP=":"; case "$(uname -s)" in MINGW*|MSYS*|CYGWIN*) SEP=";";; esac
HERE="$(pwd -W 2>/dev/null || pwd)"
mkdir -p build
export LEAN_PATH="$HERE/build$SEP$P/mathlib/.lake/build/lib/lean$SEP$P/plausible/.lake/build/lib/lean$SEP$P/LeanSearchClient/.lake/build/lib/lean$SEP$P/importGraph/.lake/build/lib/lean$SEP$P/Qq/.lake/build/lib/lean$SEP$P/aesop/.lake/build/lib/lean$SEP$P/batteries/.lake/build/lib/lean$SEP$P/proofwidgets/.lake/build/lib/lean"
ORDER="CollatzElementary CollatzSeparation LemmaE CollatzCrossing CollatzPhase CollatzConstants CollatzRuns CollatzCylinders CollatzSpend CollatzFirstReturn CollatzExamples"
if [ "$#" -gt 0 ]; then ORDER="$*"; else rm -rf build; mkdir -p build; fi
for m in $ORDER; do
  "$LEAN" -o "build/$m.olean" "$m.lean" > "build_$m.log" 2>&1; code=$?
  nw=$(grep -c "warning" "build_$m.log"); ns=$(grep -c "sorry" "build_$m.log")
  echo "$m: lean exit code $code ; warnings=$nw ; sorry-mentions=$ns"
done
