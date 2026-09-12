# RA-07 Lean formalization: statement review stage

This package prepares the full original discrete-convexity target in
[RA-07](../README.md), following Matthew J. Colbrook's
[complete Theorem 1.1](../../../references/colbrook-transfer-2026-09-11/manuscripts/01_volume_sampling_convexity.tex).
It preserves all positive spectra, every dimension at least three, and the
original indices `2 ≤ j ≤ n−1`. The sampling applications and the source's
stronger monotonicity and additional index-one assertion are outside its scope.

Formalization: **George Stepaniants**, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
Mathematical proof: **Matthew J. Colbrook**, Department of Applied Mathematics
and Theoretical Physics, University of Cambridge. AI assistance is disclosed;
no human peer review or author endorsement is claimed.

**There is no proof implementation.** The six deliberate
[Challenge](Challenge.lean) placeholders are statements to review, not proofs.
Two independent approvals of [the definitions](NLA/RA07/Definitions.lean),
[numerical and semantic targets](NUMERICAL_TARGETS.md) and Challenge must precede
any proof work. The final original target is an affirmative theorem, not a
conditional reduction assuming derivative real-rootedness or a factorization.

The intended proof uses actual finite subset sums, actual polynomial derivatives,
and an unconditional positive reciprocal-root factorization with multiplicities.
Exact finite-sum algebra gives the nonnegative second-difference certificate.
This pure algebraic argument needs no artificial interval point calculation.
LeanCert remains pinned for the later kernel trust checks of completed exports.

The package pins Lean `v4.33.1`, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.
The only statement-stage build is:

```
lake build NLA.RA07.Definitions Challenge
```

The [Comparator config](comparator.json) reserves all six exports, with no
replaceable definitions and only `propext`, `Classical.choice`, and `Quot.sound`.
Actual proof completion, final independent reviews, the completed v0.4 manifest,
and genuine Linux Comparator/kernel replay remain future gates. The canonical
status is unchanged. No commit, push or status promotion occurs at this stage.
