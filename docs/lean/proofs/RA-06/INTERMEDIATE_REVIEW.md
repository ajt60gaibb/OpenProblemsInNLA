# RA-06 independent review of intermediate proof modules

**Reviewer:** `/root/proof_inventory` (AI agent), 9 October 2026.
**Scope and verdict:** PASS for the current `Basic.lean` and `Graph.lean`
intermediate lemmas at the hashes below. This report neither approves a final
RA-06 proof nor claims `NLA.Statements.RA06.Target` has been proved. The proof
agent's Lean files were not edited during this review.

## Mathematical correspondence

`Basic.lean` uses the reviewed full target's actual `InputEnergy`, ordinary
`Sensitivity`, `RetentionProbability`, finite Bernoulli `OutcomeWeight`,
`Embedding`, and `SuccessProbability`. Its denominator-positivity lemma uses
full column rank and a nonzero vector, preserving the unrestricted supremum
domain. The sensitivity bound stays on the original ordinary row ratio.
The probability lemmas use the prescribed product law and show that the
original positive success threshold implies at least one outcome satisfying
both inequalities for **all** real test vectors simultaneously. No weaker
pointwise or expectation-only event is substituted.

The numerical support lemmas retain real `p`, the non-strict embedding
comparison, and the source's `4ε + 2k/R` witness inequality. Their conclusion
is the exact disjunction `Rε ≤ k ∨ (6ε)^(-p) ≤ k`; the graph argument must
still establish the comparison premise for the concrete weighted graph.
`Graph.lean` represents each unordered complete-graph edge once as a strictly
ordered pair. Its singleton potential and edge-energy identities yield the
correct unweighted degree and weighted-degree bounds from an all-potential
energy embedding. Its `WeightedEnergy` permits arbitrary real weights at this
stage; the future support/crossing-weight argument must explicitly require
nonnegative weights, as the source does.

These modules do not yet connect graph energies to a grounded full-rank
incidence matrix, compute equal row sensitivities, derive common `q` with the
exact `1/n` floor and cap, prove the support-witness energy comparison, or
finish the expected-size and asymptotic contradiction. Those are required for
the frozen negative `Target`; none can be replaced by an assumed theorem or
axiom.

## Trust and elaboration

With Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`
and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, I ran:

```sh
cd lean-statements
lake build NLA.Proofs.RA06.Graph
lake env lean /private/tmp/RA06IntermediateTrust.lean
```

Both commands exited 0; Lake reported `Build completed successfully (2013
jobs)`. The second source imported `NLA.Proofs.RA06.Graph` and
`LeanCert.Tactic.Verification`, set `leancert.trust` to `"kernel"`, and applied
`#assert_trust kernel` to `inputEnergy_pos`, `sensitivityRatio_mem_unit`,
`retentionProbability_pos`, `sum_outcomeWeight_eq_one`,
`exists_embedding_of_target_probability`, `supportDegree_lower_bound`,
`witnessComparison_forces_support_bound`, and `weightedDegree_bounds`.
The two printed transitive axiom sets were exactly
`[propext, Classical.choice, Quot.sound]`; the module's own reports show the
same three axioms for every current lemma. The temporary audit source has
SHA-256 `c894a3b5eb98347afc5858973acd8b4e5b02c7555084c12de4eee2c944bb0ecc`.
The source scan found no `axiom`, `sorry`, `admit`, `unsafe`, `opaque`,
`constant`, `native_decide`, `implemented_by`, or `run_tac` in either file.
`#assert_trust kernel` checks transitive dependencies and excludes custom,
sorry, and native-compiler axioms.

## SHA-256 of reviewed inputs

| Repository-relative path | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-06/README.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.tex` | `21c5187b695e4469d803ceced320bd0314ade4702ed4567160f8ff835122cec7` |
| `docs/lean/statements/RA-06/NUMERICAL_TARGETS.md` | `7036e298c8f74c4693fb638daf1aa22778756a9c26c53fbc39a9341e85f3d5e8` |
| `lean-statements/NLA/Statements/RA06.lean` | `865af15803905e04de1202266f5af75fc5486b8345fdba25a44052202742883d` |
| `lean-statements/NLA/Proofs/RA06/Basic.lean` | `ec62967a166fca9f03cce1edb7b975314e7b644c6424fdb31c854b684439521f` |
| `lean-statements/NLA/Proofs/RA06/Graph.lean` | `d6f5d98abbb1951262f39b2c4f1238488175f689eae32f25b56e9daa11cbeb79` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
