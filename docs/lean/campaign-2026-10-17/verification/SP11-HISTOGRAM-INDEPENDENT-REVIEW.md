# SP-11 HistogramRigidity — independent review

Reviewer: `/root/lean_verification`, independent Codex AI agent, 17 October
2026. I did not implement this module. **Verdict: approve.**

Reviewed source: `lean-statements/NLA/Proofs/SP11/HistogramRigidity.lean`,
SHA-256 `93d252876b92c2ab6e72033ffe982f92e88bc93f265d24f2832be6273bb110ca`.

`weight_sum_eq_of_occurrence_histogram_eq` applies the genuine natural-linear
map `Finsupp.linearCombination ℕ weight` to equality of the two finite sums of
single-variable exponents. Additivity and the single-basis evaluation give
exact equality of the sums of arbitrary natural-valued variable weights.
There is no injectivity assumption on occurrence-to-variable maps, no ordering
of the variable type, and no omitted multiplicity for repeated variables.

`occurrence_weight_eq_of_histogram_eq` assumes a canonical lower bound for
each occurrence. If one actual weight strictly exceeded its lower bound,
finite-sum strict monotonicity would contradict the total equality from the
first lemma. Thus the pointwise conclusion is valid, including empty sets
and repeated variable names. The graph-specific bounds and recovery of conduit
colors remain explicit external proof obligations. These lemmas do not assert
the unique-monomial theorem or an unconditional graph representation.

The implementation directly reuses Mathlib's linear-combination and ordered
finite-sum APIs. I independently froze and compiled the module in a fresh
private output prefix, then ran a separate consumer requiring both exported
names to be theorem constants and auditing kernel trust and transitive axioms.
Both commands passed; each theorem has only `propext`, `Classical.choice`,
`Quot.sound`. All ten dependency revisions/tracked sources passed before and
after, and the reviewed module was unchanged during execution.

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-histogram.py
```

Exact source snapshots, raw Lean logs, consumer source, dependency checks and
machine-readable result are retained under `sp11-histogram-review/`. This is
local macOS proof elaboration/LeanCert kernel-trust evidence with trusted pinned
compiled dependencies, not a new Linux Comparator run or complete SP-11 proof.
