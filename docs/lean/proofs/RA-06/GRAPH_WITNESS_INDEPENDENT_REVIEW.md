# RA-06 support witness: independent proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026.
**Scope:** frozen `GraphWitness.lean` at the SHA-256 below, compared with the
canonical RA-06 README, the frozen negative Target, and Theorem 3.1 of the
preserved complete-graph manuscript. I did not edit proof source.
**Verdict:** the per-vertex arbitrary-nonnegative-weight support obstruction
has the stated exact numerical scope and passes local LeanCert kernel checks.
This is an intermediate theorem, **not** a proof of the full RA-06 Target.

## Exact theorem statement and source correspondence

The decisive export is
`NLA.Proofs.RA06.supportDegree_lower_of_approx`. Its actual hypotheses
are `p>1`, `0<ε<1/2`, natural `v>1`, an arbitrary nonnegative real weight
`w : Edge v→ℝ`, and **simultaneous** two-sided approximation for every real
potential `z : Fin v→ℝ`:

```text
(1−ε)*CompleteEnergy p z ≤ WeightedEnergy p w z
                         ≤ (1+ε)*CompleteEnergy p z.
```

For **each** vertex `u`, it proves the exact disjunction

```text
(v−1)*ε ≤ SupportDegree w u  OR
(6*ε)^(−p) ≤ SupportDegree w u.
```

This is equivalent to the manuscript's
`κ_u≥min{(v−1)ε,(6ε)^(−p)}`. Its support degree counts distinct neighbors
joined by **positive** edges, rather than the weighted degree; the weights
may be unequal and need not arise from independent Bernoulli sampling. The
Lean theorem works already for `v>1`; retaining `ε<1/2` matches the source
and canonical tolerance range, although its final numerical helper needs
only `ε>0`. There is no fixed `p`, vertex, or test potential hidden in the
conclusion. For the canonical RA-06 target, `p>2` supplies `p>1`.

The proof's finite graph identities match the source obstruction:

1. `SupportNeighbors w u` is the set `W` of positive-weight neighbors and
   `OutsideNeighbors w u` is the disjoint complement `O` after removing
   `u`. `edgeOfCross` maps each ordered `W×O` pair injectively to its one
   unordered complete-graph edge. `crossEnergy_le_complete` therefore
   bounds the selected crossing energy by the full finite graph energy,
   counting every edge at most once.
2. The support-dependent `WitnessPotential` takes value `1` at `u`, value
   `t=k^(−1/p)` on `W`, and zero on `O`, where
   `k=SupportDegree w u`. `supportDegree_pos` from the graph module proves
   `k>0` from the embedding, so the negative real power is taken at a
   strictly positive base. `inversePower_balance` proves **exactly**
   `k*t^p=1` for positive real `p,k`. The selected center-to-`O` and
   `W`-to-`O` cuts have energy `(R−k)(1+k*t^p)=2(R−k)`, with
   `R=v−1`; `witness_completeEnergy_lower` proves this as a lower bound
   on the actual `CompleteEnergy`. The source gives the stronger equality
   `F(z)=2(R−k)+k(1−t)^p`. Dropping its nonnegative last term is a valid
   intermediate simplification and still yields the same final obstruction.
3. `witness_edge_upper` handles each **positive** weighted edge. A supported
   center edge has power `(1−t)^p`; a non-center edge has zero power if both
   endpoints lie on the same side, while a nonzero crossing edge is charged
   to at least one positive supported neighbor. Summation and the exact
   singleton weighted-degree upper bound give
   `U_w(z)≤(1+ε)R(1+(1−t)^p)`. The counting may overcharge an edge meeting
   two neighbors, which is safe for this upper bound. No common weight or
   sampler probability is assumed.
4. The lower half of the **same all-vector** approximation applied to this
   support-dependent `z` combines the preceding estimates into
   `2(1−ε)(R−k)≤(1+ε)R(1+(1−t)^p)`. The existing kernel-checked
   `weakWitnessComparison_forces_support_bound` converts that exact
   comparison to the displayed disjunction, using
   `(1−t)^p≤1−t` for `p>1` and the constant `6` from
   `t≤4ε+2k/R`. The complete and weighted bounds use the same `w,u,p,ε`.

Thus the theorem proves the manuscript's local degree obstruction without
replacing the original ordinary-sensitivity sampler by an assumption in
the eventual Target. The arbitrary-weight condition is a stronger
intermediate setting that can be instantiated with the target's sampled
reciprocal weights through `embedding_to_weighted` and
`sampleWeight_nonneg`.

## Kernel result and remaining finite bridges

With pinned Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, I ran from
`lean-statements`:

```sh
lake build NLA.Proofs.RA06.GraphWitness
lake env lean NLA/Proofs/RA06/GraphWitness.lean
lake env lean /private/tmp/ra06-graphwitness-independent-audit.lean
```

All exited zero; Lake completed 2,061 jobs and the direct call freshly
elaborated the source. The separate audit imports the module and
`LeanCert.Tactic.Verification`, sets `leancert.trust "kernel"`, and runs
`#assert_trust kernel` on all 16 public GraphWitness theorems, including
`witness_completeEnergy_lower`, `witness_weightedEnergy_upper`, and the
final `supportDegree_lower_of_approx`. Direct and audit `#print axioms`
for the main theorems report exactly `[propext, Classical.choice,
Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`,
`opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or
`run_tac` token.

The file does **not** yet sum the per-vertex disjunction into the global
support lower bound. In particular, under `R*ε≥(6ε)^(−p)` one must select
the common lower threshold `(6ε)^(−p)` for every vertex, apply the
already-proved handshake identity, and transfer the resulting positive-edge
count to `RetainedCount kept`. The Bernoulli expectation then needs the
explicit success factor `1−δ`, followed by the graph dimension, sensitivity
budget, logarithm, and final `∀p>2` negation bridges. The frozen Target is
still only a proposition definition, with no theorem inhabiting it; no
Linux Comparator result for RA-06 is claimed.

## SHA-256 of reviewed inputs

| Repository-relative input, except the temporary audit | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-06/README.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.tex` | `21c5187b695e4469d803ceced320bd0314ade4702ed4567160f8ff835122cec7` |
| `lean-statements/NLA/Statements/RA06.lean` | `865af15803905e04de1202266f5af75fc5486b8345fdba25a44052202742883d` |
| `lean-statements/NLA/Proofs/RA06/Basic.lean` | `af6f79d018f64fe09204683705dbee39614d8b7e77ce301c33b58cd7e3e2e5a3` |
| `lean-statements/NLA/Proofs/RA06/GraphSupport.lean` | `15d530acbd8a823d45582c5620fc89a3ebe1bfd8bcd2e7a6491e1d0087f535a8` |
| `lean-statements/NLA/Proofs/RA06/GraphSupportCount.lean` | `2447bf20d910f2393a5317d4c1a7c63696a522aef9b91d8fbb7df1abc779f87b` |
| `lean-statements/NLA/Proofs/RA06/GraphSampling.lean` | `0f94b12262f18313b607907fe2f9aeb2d071fb7901d0f56a8e21e97085610e8a` |
| `lean-statements/NLA/Proofs/RA06/GraphWitness.lean` | `cc1ded7324a6520ba901727bd0c7bce046b6f34bbc8b76906f152624902d5cd6` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `/private/tmp/ra06-graphwitness-independent-audit.lean` | `6ba9e7020f33e6899ade4cc6edbf9fd9cc782dfb07cb3f833ac293537b76223b` |
