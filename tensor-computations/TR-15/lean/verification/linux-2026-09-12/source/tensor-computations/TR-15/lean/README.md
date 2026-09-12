# TR-15: formal counterexample to Hankel H-eigenvalue inheritance

The complete seven-export proof has passed local Lean elaboration, kernel trust
and transitive axiom checks, two independent statement reviews before
implementation, and two independent final proof reviews. It is a reviewed Linux
candidate. Actual Linux sandboxed Comparator, default-kernel replay, negative
controls and independent operational audit are pending. The canonical problem
remains **Solved**; this candidate does not claim a Lean-verified status.

The mathematical counterexample is Matthew J. Colbrook's, in the
[complete retained source](../../../references/colbrook-unclaimed-2026-09-11/manuscripts/TR-15.md).
The formalization author is George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA. This work is AI-assisted; the retained independent review reports
identify their actual scope. No human peer review or source-author endorsement
is claimed, and no personal email is included.

The [complete original target](../README.md) still quantifies every odd `m≥3`,
every integer `q≥2`, every dimension `n≥2`, and every real common generator of
length `qm(n−1)+1`. Actual Hankel arrays, every ordered contraction tuple,
signed coordinate powers and nonzero real H-eigenvectors are represented. No
strong-Hankel, associated-matrix positivity or eigenpair-existence assumption is
added to the original implication.

The exact witness is `m=3`, `q=2`, `n=2`, with the shared generator
`h=(2,0,1,0,2,0,−1)`. Its order-three, dimension-three tensor has strictly positive
real H-eigenvalues, proved universally from the sum-of-squares first contraction.
The order-six, dimension-two tensor has the genuine negative H-eigenpair
`(−1,(0,1))`. The higher contraction is reduced to the single surviving tuple;
the proof does not enumerate candidate eigenvalues or assume tensor coefficients.

Nonvacuity is also proved: the actual polynomial
`2t⁴+2t³+3t²−4t−1`, whose endpoint values are `−1` and `2`, has a root `t∈(0,1)`
by Mathlib's intermediate value theorem. It gives a nonzero lower eigenvector
`(1,0,t)` and eigenvalue `2+2t+2t²`, satisfying all component equations. This
existence result is a separate conclusion, not a premise added to the conjecture.

- [Exact numerical and quantified statements](NUMERICAL_TARGETS.md).
- [Canonical and complete-source correspondence](SOURCE_CORRESPONDENCE.md).
- [Actual mathematical definitions](NLA/TR15/Definitions.lean).
- [Independent challenge signatures](Challenge.lean).
- [Complete implementation](NLA/TR15/Proof.lean).
- [All seven complete public statements](Solution.lean).
- [All seven registered exports](comparator.json).
- [Exact v0.4 publication metadata](formalization.yaml).
- [Completed local proof and build record](reviews/proof-completion.md).
- [Exact supplementary reconstruction](reviews/source-numerical-reconstruction.json).

The project pins Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. From this directory, build the actual
implementation with:

```
lake build Solution
```

LeanCert checks the exact inequality `−1<0` in explicit kernel mode on a singleton
interval. Its proof is retained in the final contradiction. Exact algebra proves
the contraction identities and sum-of-squares argument; the existence theorem
uses the actual IVT, without numerical root isolation. All 15 distinct internal
and public declarations pass kernel trust assertions and have exactly
`propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Independent
inspections repeat the seven public checks. The seven deliberate Challenge
placeholders are statement-only and never imported by the implementation;
they are excluded from proof-development sorry counts.

The independent reviews are [statement referee 1](reviews/statement-referee-1.md),
[statement referee 2](reviews/statement-referee-2.md),
[final referee 1](reviews/proof-referee-1.md) and
[final referee 2](reviews/proof-referee-2.md). Both final referees freshly
re-elaborated source in separate object prefixes and inspected the actual proof
terms. These macOS checks reused ten verified clean pinned dependency caches;
they do not claim full dependency-source rebuilds or a project-specific Linux run.

The [proof freeze](reviews/proof-freeze.json),
[statement gate](reviews/statement-gate.json) and all previous review evidence
remain unchanged. Their phase labels describe historical checks. The old
statement-stage README is preserved as [the frozen README](verification/linux-candidate-2026-09-12/frozen-statement-stage-README.md).
Only this current README changes among the 75 frozen project inputs; all 74
others and all six original canonical/manuscript sources remain byte-identical.

The project follows the repository's [Tau Ceti review adaptation](../../../docs/lean/REVIEW.md)
and [Lean verification protocol](../../../docs/lean/README.md). Schiffer and
Forsythe informed workflow organization; their mathematical results are not
assumed. Mathlib, LeanCert and shared checker attribution and licenses remain
separate from the original counterexample and formalization authorship.
