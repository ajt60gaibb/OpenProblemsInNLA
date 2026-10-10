# RA-06 independent review: grounded graph matrix and sensitivity bound

**Reviewer:** `/root/proof_inventory` (AI agent), 9 October 2026.
**Scope:** `Basic.lean`, `Graph.lean`, `GraphCounting.lean`, `GraphPower.lean`,
`GraphSensitivity.lean`, and `GraphMatrix.lean` at the hashes below. The proof
source was not edited in this review. **Verdict:** the current intermediate
theorems are sound and kernel checked; the total-sensitivity estimate is
weaker than the source manuscript's explicit coefficient. This is not a
review or proof of the final `NLA.Statements.RA06.Target`.

## Mathematical and numerical checks

- `GraphMatrix d` has one row for each `Edge (d+1)`, where an edge is a pair
  `a<b`. Its `edgeIndex` equivalence enumerates each unordered complete-graph
  edge exactly once. The source grounds the last vertex; this implementation
  grounds vertex zero with `Fin.cons 0 x`. Relabeling vertices makes these
  equivalent. `graphMatrix_rowValue` proves each row acts as the oriented
  potential difference at its endpoints. The proof of
  `graphMatrix_fullColumnRank` uses the actual row for edge `(0, Fin.succ j)`
  to infer `x j=0` from a zero matrix action, for every column `j`. It does
  not assume full column rank.
- `graphMatrix_inputEnergy` rewrites the **original** `InputEnergy` of the
  matrix as `CompleteEnergy p (GroundPotential x)` by the edge-index
  equivalence and the row-value identity. The result is equality of the
  whole finite sums, with no normalized or approximate energy and no
  restriction on `p`. The complete graph counts each edge once.
- `GraphCounting.incidentEdgeEquivOther` and `incident_card` prove exactly
  `v−1` edges incident at each vertex. The star sum includes precisely the
  edges from the selected vertex to every other vertex. Its nonnegative
  complement gives the star-to-complete-energy inequality. `GraphPower`
  proves the convexity-based two-leg bound for real `p≥1`; summing over
  every third vertex in `GraphSensitivity` yields
  `v*|z_i-z_j|^p ≤ (2*2^(p−1))*CompleteEnergy p z`.
- `graphMatrix_sensitivity_le` applies that inequality to every input `x`
  and calls `sensitivity_le_of_rowEnergy_bound` from `Basic.lean`. That
  lemma unfolds the frozen `Sensitivity` as the `sSup` over **all nonzero**
  real `x`, proves the set nonempty using `d>0`, and uses full column rank to
  prove the denominator positive. The result therefore bounds the original
  ordinary sensitivity, not a proxy or a restricted test set. Its exact
  stated constant is `(2*2^(p−1))/(d+1) = 2^p/(d+1)`.
- `graphMatrix_totalSensitivity_bound` sums those row bounds and uses the
  safe edge-count inequality `card Edge(d+1) ≤ (d+1)^2`. It proves
  `TotalSensitivity(GraphMatrix d,p)+d ≤ (2*2^(p−1)+1)*(d+1)`, namely
  `(2^p+1)*(d+1)`, for `d>0`, `p≥1`. The **left side is the exact original**
  `TotalSensitivity+d` expression. The manuscript instead proves equal row
  sensitivities `1/(1+(v−2)*2^(1−p))` and the sharper bound
  `TotalSensitivity+d ≤ (2^(p−2)+1)*v`, with `v=d+1`. Neither equality nor
  that coefficient is currently a theorem in these modules. The coarser
  estimate remains a valid `O_p(d)` bound for a full-target contradiction,
  but the source's explicit `β_p` or `γ_p` constants cannot be quoted from
  it unchanged. Any later use must prove the sharper statement or recompute
  the constants from `2^p+1`.

The source manuscript and frozen numerical specification state the exact
sensitivity and `(2^(p−2)+1)*v` coefficient. The current graph modules are
intermediate results; they do not yet prove the common Bernoulli probability,
the support obstruction, or the asymptotic contradiction for every `p>2`.

## Reproducible kernel audit

The project pins Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. With the pinned Lean
executable on `PATH`, I ran from `lean-statements`:

```sh
lake build NLA.Proofs.RA06.GraphMatrix
lake env lean NLA/Proofs/RA06/GraphMatrix.lean
lake env lean /private/tmp/ra06-graphmatrix-audit.lean
```

All exited zero. Lake reported `Build completed successfully (2056 jobs)`;
the direct `lean` invocation freshly elaborated `GraphMatrix.lean`. The
temporary audit imported that module and LeanCert's verification tactic,
set `leancert.trust` to `"kernel"`, and ran `#assert_trust kernel` on
`incident_card`, `sum_differences_le_complete`,
`abs_sub_rpow_le_two_legs`, `pairPower_le_complete`,
`graphMatrix_fullColumnRank`, `graphMatrix_inputEnergy`,
`graphMatrix_sensitivity_le`, and `graphMatrix_totalSensitivity_bound`.
All passed. The four major matrix exports printed exactly the transitive
axioms `[propext, Classical.choice, Quot.sound]`. A source scan across the
six reviewed proof modules found no `axiom`, `sorry`, `admit`, `unsafe`,
`opaque`, `constant`, `native_decide`, `run_tac`, or `implemented_by` tokens.
These checks certify the stated intermediate theorems, not the truth of the
unproved final negative Target.

## SHA-256 of reviewed inputs

| Repository-relative path | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-06/README.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.tex` | `21c5187b695e4469d803ceced320bd0314ade4702ed4567160f8ff835122cec7` |
| `docs/lean/statements/RA-06/NUMERICAL_TARGETS.md` | `7036e298c8f74c4693fb638daf1aa22778756a9c26c53fbc39a9341e85f3d5e8` |
| `lean-statements/NLA/Statements/RA06.lean` | `865af15803905e04de1202266f5af75fc5486b8345fdba25a44052202742883d` |
| `lean-statements/NLA/Proofs/RA06/Basic.lean` | `af6f79d018f64fe09204683705dbee39614d8b7e77ce301c33b58cd7e3e2e5a3` |
| `lean-statements/NLA/Proofs/RA06/Graph.lean` | `d07a834d3845d52d2f764406e74e344024b518afa758d53a638e665d924b90b1` |
| `lean-statements/NLA/Proofs/RA06/GraphCounting.lean` | `fe5f4c37e19d58fa644a734167824c6476577507ccff413ce6c2d7d69b430193` |
| `lean-statements/NLA/Proofs/RA06/GraphPower.lean` | `fdb106957649e526fd7ab84a718374e243fab6e76d5609dfb25194690d2a9476` |
| `lean-statements/NLA/Proofs/RA06/GraphSensitivity.lean` | `953ae1b6041d39d82bb371afc3f4bfe6c2c5f4759bacb77836dad40cd7ff3631` |
| `lean-statements/NLA/Proofs/RA06/GraphMatrix.lean` | `aed5d4d668004e1b03ad6b98e73db1573d6fa9743a93f0cf34fc1b4c813e28ec` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| temporary LeanCert audit source, `/private/tmp/ra06-graphmatrix-audit.lean` | `7dfd531db321b82ee5239a41cff57565af9001039c4edf3086b1996fc0a5cf66` |
