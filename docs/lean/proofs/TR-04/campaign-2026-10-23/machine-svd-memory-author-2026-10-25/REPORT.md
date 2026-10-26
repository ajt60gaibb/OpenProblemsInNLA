# TR-04 exact SVD output-memory author replay

Author `/root/recover_geometry`, 2026-10-25. One new source `MachineSVDMemory.lean` is frozen by source-lock SHA-256 `d82b1ad398e4c13e69acfe21c074759f0917300ebe05b117f1d4728431fa8525`. Its source SHA-256 is `6b1663e4df0847690b296475a5b255c4e9f6a8318a55742d2f7f7d3c8feee043`.

The proof uses the unchanged literal `matrixCell`, `readMatrix`, `writeSVD`, and `OutputBlocksDisjoint`. Generic row-major lookup gives every matrix entry. Readback returns U exactly, every sigma entry exactly, and V exactly; every address outside all three half-open blocks keeps its old value. The U and outside-cell lemmas need no disjointness assumption; sigma and V use precisely the literal model condition. All natural dimensions, including zero, are covered without extra hypotheses. These statements do not constrain or select singular bases.

Fresh author replay passed two project source compilations (unchanged machine model and new support) and a separate exact-type conjunction consumer. All ten new declarations passed kernel assertions; printed axiom lists contain only the three standard axioms. No project objects were reused. The pinned Mathlib/LeanCert external cache was reused. Lean 4.33.1 compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` checked the result. The prior radix/recursive closure and all 25 original review inputs are unchanged.

Receipt `run/result.json` SHA-256: `eee50d60a60c43a86d1b960ada1360f41fe930d1fe0ee17b290637be2f99f7da`. This is author support evidence, not independent approval, a complete TT program, Target, runtime bound, Linux CI or Comparator acceptance.

Reproduce with `python3 docs/lean/proofs/TR-04/campaign-2026-10-23/machine-svd-memory-author-2026-10-25/replay.py --output /absolute/new/output`.
