# IE-06: complete local Lean proof

[Solution.lean](Solution.lean) proves the complete original IE-06 target and a
stronger all-Schur probability bound. The complete probabilistic argument is
implemented; its final theorems have compiled with LeanCert in kernel mode and
only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom
closures. The fresh local run **passed**: all 114 source modules compiled,
3,229 owned declarations across 113 concrete modules passed the transitive
axiom audit, both rejection controls failed as required, and the unchanged
Comparator library accepted all six actual Solution exports against the
independent frozen Challenge. See the
[final receipt](verification/local/attempt-0i_0ibma/result.json) and
[Comparator log](verification/local/attempt-0i_0ibma/CompareSolution.lean.log).
No authoritative Linux sandbox, exporter, or separate raw-kernel replay is
claimed; [verification/SUMMARY.md](verification/SUMMARY.md) records these limits.

The permanent ID, canonical path, original mathematical target, and canonical
README/TeX/PDF were preserved by this task. The working page already recorded a
literature resolution when work began. Complete verbatim copies of both the
original HEAD page and the preexisting working page are retained in
[source/](source/). Nothing has been committed, pushed, or submitted as a pull
request; no remote CI was dispatched. John Urschel has not been contacted.
Publication remains for the maintainer to decide after speaking with him.

## Exact target and stronger result

The original proposition is [`SquareRootUpperBound`](NLA/IE06/Statements.lean):

```lean
∀ η : ℝ, 0 < η →
  Tendsto (fun n : ℕ => gaussianMatrix n
    (exceedanceEvent n ((n : ℝ) ^ ((1 : ℝ) / 2 + η)))) atTop (𝓝 0)
```

`gaussianMatrix` is the actual product law of independent standard normal
entries. The growth factor uses exact partial pivoting, every active Schur
complement including the input and final scalar complement, and normalization
by the largest absolute input entry. `exceedanceEvent` asserts existence of a
bad admissible pivot path, so the theorem covers every admissible tie choice.
The event has explicit positive-dimension and nonsingularity guards. Its
Gaussian probability is not conditioned on successful elimination; the
singular exceptional set is proved null. The dimension-zero event is empty.

The proved `SchurSubpolynomialTail` says: for each $\alpha>0$, there are
$C>0$ and $N\ge2$, depending only on $\alpha$, such that every $n\ge N$ satisfies

$$
\Pr\!\left\{\rho_n>\sqrt n\exp\!\left(C\sqrt{\log n}\right)\right\}<n^{-\alpha},
$$

where the event covers all admissible paths as above. The proof in
[Unconditional.lean](NLA/IE06/Unconditional.lean) supplies every probability
estimate; [Reduction.lean](NLA/IE06/Reduction.lean) then derives the original
limit for every $\eta>0$.

[Urschel's manuscript, arXiv:2610.06785v1](https://arxiv.org/abs/2610.06785v1),
displays an LU-growth statement as Theorem 1.4. The stronger all-Schur estimate
here is extracted from the Section 5 argument, with the elimination,
normalization, and almost-sure tie bridges proved explicitly. The two growth
definitions are not identified. IE-06 has one original target. Historical
partial results are context; no additional open IE-06 problem is invented.

## Proof and review map

[PROOF_STATUS.md](PROOF_STATUS.md) describes the complete chain: Gaussian
foundations and actual pivot conditioning; Gaussian spectral and inverse
estimates; selected-block extension and recursion; smoothing of elimination
rows; the all-Schur growth transfer; and the final rate and limit.
[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) and the
[statement specification](reviews/statement-specification.md) preserve the
scope and conventions. Symbolic estimates avoid enumeration of large matrices
or evaluation of a huge asymptotic cutoff.

All six exported results are in `Solution.lean` and selected exactly once by
[comparator.json](comparator.json):

| Declaration in `NLA.IE06` | Result |
| --- | --- |
| `squareRootUpperBound` | The complete original IE-06 limit |
| `schurSubpolynomialTail` | The stronger all-Schur tail bound |
| `gaussianMatrix_probability` | Probability normalization in every dimension |
| `exceedanceEvent_measurable` | Measurability for every dimension and real threshold |
| `admissiblePath_exists` | An admissible path for every nonsingular input |
| `gaussianMatrix_singular_null` | Gaussian singular-set nullity in every dimension |

There are no unresolved proof-development `sorry` declarations or assumed
literature theorems in these results. [Challenge.lean](Challenge.lean) remains
the verbatim historical reference interface with six deliberate placeholders;
its header describes the initial statement phase. It is never imported by
`Solution.lean`. Comparator has no replaceable definition holes.

Multiple AI agents reviewed exact mathematical and numerical contracts before
implementation, and different agents reviewed actual source and hash-bound
build evidence afterward. Reports under [reviews/](reviews/) identify their
scope and source hashes. The
[final independent mathematical scope audit](reviews/final-independent-mathematical-scope-audit.md)
approved the original-target correspondence and complete proof connections.
These are AI-agent reviews, not human peer review or source-author endorsement. Pinned adopted proofs of Prékopa–Leindler, Gaussian
Lipschitz concentration, and singular-value infrastructure retain their sources,
licenses, and compatibility records under `source/`.

## Reproduction and trust boundary

The package pins Lean 4.33.1, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and its full dependency graph.
[INFRASTRUCTURE.md](INFRASTRUCTURE.md) gives the reproduction commands and
shared CI/Comparator workflow. [formalization.yaml](formalization.yaml) records
all six proved exports, zero proof-development sorries, and the permitted
foundational axioms.

Local checking uses pinned, read-only dependency caches. The fresh checker
rebuilt every project source, audited owned declarations including private
helpers, exercised the `sorry` and native-execution rejection controls, and ran
the pinned Comparator library on the actual independent Challenge and Solution
environments. All checks passed in `attempt-0i_0ibma`, whose input hashes match
the delivered proof sources. This local library run does not execute the full
Comparator CLI/exporter/raw-replay pipeline or the authoritative Linux sandbox.
`KernelControl.lean` proves `log(2) < 7/10` solely as a kernel-checker fixture;
the Gaussian proof does not depend on that numerical test. Shared acceptance
safeguards remain unchanged.
