# RA-06 finite support and expectation: independent proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026.
**Scope:** frozen `GraphFinite.lean` at the exact SHA-256 below, checked
against the original RA-06 sampler, the frozen Target, and the preserved
complete-graph manuscript. I did not edit proof source. **Verdict:** the
three intermediate theorems have the exact stated mathematical and
numerical scope and pass a local LeanCert kernel audit. They do **not** yet
prove `NLA.Statements.RA06.Target`.

## Exact finite and probabilistic conclusions

The original question quantifies over one full-column-rank matrix, exact
ordinary sensitivities and `q_i=min(1,1/n+s_i/α)`, an independent Boolean
sample, and one **same** `α` that must satisfy both expected-size and
simultaneous all-vector success requirements. The frozen Target negates
that claim for every real `p>2`. `GraphFinite.lean` imports the existing
grounded complete-graph matrix and the exact sampled-weight bridge; it does
not redefine this sampler or the frozen event.

1. `positiveEdgeCount_lower_of_approx` assumes `p>1`, `0<ε<1/2`,
   `v>1`, arbitrary **nonnegative** edge weights `w`, both embedding
   inequalities for **every** real vertex potential, and the dimension
   regime `(6ε)^(−p)≤(v−1)ε`. It proves
   `v*(6ε)^(−p)≤2*PositiveEdgeCount w`. This uses the exact per-vertex
   disjunction reviewed in `GRAPH_WITNESS_INDEPENDENT_REVIEW.md`: whichever
   branch a vertex satisfies, its support degree is at least the common
   threshold `(6ε)^(−p)` under the regime. The exact handshake identity
   `Σ_u SupportDegree w u=2*PositiveEdgeCount w` then gives the result.
2. `successful_retainedCount_lower` specializes `v=d+1` and the weights
   `SampleWeight d p α kept`, requiring `d>0`, `α>0`, the same
   `(6ε)^(−p)≤d ε` regime, and the frozen simultaneous
   `Embedding (GraphMatrix d) p α ε kept`. It proves **for each such
   successful outcome**

   ```text
   ((d+1)/2)*(6ε)^(−p) ≤ RetainedCount kept.
   ```

   `embedding_to_weighted` preserves every vector, while
   `sampleWeight_positive_iff` and
   `sample_positiveEdgeCount_eq_retainedCount` identify positive graph
   edges **exactly** with retained rows. Thus this is about the original
   outcome, with the original reciprocal `1/q_i` weights; no equal-
   sensitivity or common-`q` assumption is introduced.
3. `expectedSize_lower_from_graph_success` uses that per-success lower
   bound and the exact independent Bernoulli identity from `Bernoulli.lean`.
   For the same matrix, `p,ε,δ,α`, and regime, its hypothesis is the
   frozen `1−δ≤SuccessProbability (GraphMatrix d) p α ε`; its conclusion is

   ```text
   (1−δ)*(((d+1)/2)*(6ε)^(−p)) ≤
       ExpectedSize (GraphMatrix d) p α.
   ```

   The `1−δ` factor is explicit and indispensable for this arbitrary-
   weight support route. The theorem requires no sign premise on `δ` for
   this conditional inequality; the original claim later supplies
   `0<δ<1/2`. It does **not** infer an expected-size lower bound merely
   from one successful realization. The fixed choices `δ=1/4`,
   `ε=1/b` would yield coefficient `(3/4)*(6^(−p)/2)` only after a
   separate positive-base real-power rewrite. No such rewrite is hidden
   in this theorem.

These conclusions are faithful to Theorem 3.1 and Corollary 3.2 of the
preserved source: the support constant is `6^(−p)/2` after rewriting
`(6ε)^(−p)=6^(−p) ε^(−p)` for `ε>0`, and the randomized expectation
retains `(1−δ)`. The module proves the **exact pre-rewrite inequalities**
without numerical approximation. It does not claim the source's sharper
common-probability obstruction, which would omit the success factor.

## Reproducible kernel check and remaining Target bridge

Using the statement project's pinned Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, I ran from
`lean-statements`:

```sh
lake build NLA.Proofs.RA06.GraphFinite
lake env lean NLA/Proofs/RA06/GraphFinite.lean
lake env lean /private/tmp/ra06-graphfinite-independent-audit.lean
```

All commands exited zero. Lake completed 2,062 jobs. The direct call
freshly elaborated the frozen source; the separate file imported it and
`LeanCert.Tactic.Verification`, set `leancert.trust "kernel"`, and ran
`#assert_trust kernel` on all three public theorems. Direct and audit
`#print axioms` reported only `[propext, Classical.choice, Quot.sound]`.
The source scan found no `sorry`, `admit`, custom `axiom`, `opaque`,
`unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` token.

The full Target still needs the natural ceiling/dimension bridge for
`v=⌈b^(p+2)⌉`, graph edge count and the exact raw budget logarithm,
`TotalSensitivity+d≤(2^p+1)v`, the appropriate arbitrary-weight
coefficient separation, and an actual theorem deriving contradiction
from **every** proposed positive `C,c` using the original
`OriginalPositiveClaim` quantifiers. Until that theorem is proved and
Comparator accepts it, RA-06 remains partial.

## SHA-256 of reviewed inputs

| Repository-relative input, except the temporary audit | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-06/README.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.tex` | `21c5187b695e4469d803ceced320bd0314ade4702ed4567160f8ff835122cec7` |
| `lean-statements/NLA/Statements/RA06.lean` | `865af15803905e04de1202266f5af75fc5486b8345fdba25a44052202742883d` |
| `lean-statements/NLA/Proofs/RA06/GraphWitness.lean` | `cc1ded7324a6520ba901727bd0c7bce046b6f34bbc8b76906f152624902d5cd6` |
| `lean-statements/NLA/Proofs/RA06/GraphSupportCount.lean` | `2447bf20d910f2393a5317d4c1a7c63696a522aef9b91d8fbb7df1abc779f87b` |
| `lean-statements/NLA/Proofs/RA06/GraphSampling.lean` | `0f94b12262f18313b607907fe2f9aeb2d071fb7901d0f56a8e21e97085610e8a` |
| `lean-statements/NLA/Proofs/RA06/Bernoulli.lean` | `5da1edcb106c85ea14255b2b975f137a1ed39b0c7332088c8b15170b8b33d5b4` |
| `lean-statements/NLA/Proofs/RA06/GraphFinite.lean` | `65012435863c6302c5bf82efcca4617d50edbf75c0a921f88528dc673301e70b` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `/private/tmp/ra06-graphfinite-independent-audit.lean` | `852ded53fb966d771037acd1bfb598818740bdbf39cf10020cb34b1cc5a1e248` |
