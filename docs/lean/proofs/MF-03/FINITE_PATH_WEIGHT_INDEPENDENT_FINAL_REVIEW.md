# MF-03 finite path weight: independent final review

**Author:** `/root/mf03_jt_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this exact partial gate; the path/tableau bijection remains open.

The frozen source `FinitePathWeight.lean` has SHA-256 `5254564d9a0540c284c127dc9ec4f656f4dfa66ba386a5a3faf62937ea0adefe`. I checked it against the approved finite path endpoint/tableau precontract and the literal `finiteBidiagonal`, `finiteValidStep`, `finiteStepWeight`, `finiteValidPathWeight`, and `finiteAdvanceLabels` definitions. A valid first step is stationary or advances exactly one position. Its literal matrix entry is respectively `1` or `cosineFactor(N+1)` at first factor label `N`; the induction multiplies all paths' factors and records each fresh label once. The public theorem gives, for every `m,N` and every valid chain, the exact equality of the chain weight to `∏ p:Fin m, ∏ k∈finiteAdvanceLabels ... p, cosineFactor(k+1)`, with zero-based labels and no numerical approximation. Empty dimensions and empty chains remain quantified.

An independent imported audit at `/private/tmp/mf03-finite-path-weight-independent-audit.lean`, SHA-256 `a48a67c712ff2a76b058a1d8776e0b7ed2dec6279ee1ec8e50268153604d0e69`, elaborated the exact public signature, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`. No proof escape or new axiom appears in the source.

This product identity does not yet prove that valid chains correspond to semistandard tableaux, equality of their weighted sums, determinant positivity, signed Cramer bounds, or the all-order MF-03 Target.
