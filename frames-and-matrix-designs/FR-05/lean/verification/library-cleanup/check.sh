#!/usr/bin/env bash
# Run from any directory; no dependency updates, commits, or remote writes.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."

lake build NLA Solution Challenge

# Keep the curated reusable layer free of applicable mathlib syntax-linter warnings.
# Older application modules are built above, but are not claimed to be lint-clean.
for source in \
  NLA/FR05/Geometry/Obstruction.lean \
  NLA/FR05/Measure/Comparison.lean \
  NLA/FR05/Gaussian/GaussianFrameRows.lean \
  NLA/FR05/Gaussian/GaussianGram.lean \
  NLA/FR05/SmallBall/GaussianSmallBall.lean \
  NLA/FR05/Overlap/HaarCorner.lean \
  NLA/FR05/Overlap/Spectrum.lean; do
  lake env lean -Dlinter.mathlibStandardSet=true -DwarningAsError=true "$source"
done

lake env lean -DwarningAsError=true verification/library-cleanup/Api.lean
lake env lean -DwarningAsError=true verification/library-cleanup/Inspect.lean

if rg -n '\b(sorry|admit|axiom|native_decide|unsafe)\b' NLA Solution.lean; then
  echo 'Unexpected proof placeholder or nonstandard trust declaration.' >&2
  exit 1
fi
