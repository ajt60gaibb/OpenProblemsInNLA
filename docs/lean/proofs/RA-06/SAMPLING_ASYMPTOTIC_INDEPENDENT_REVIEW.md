# RA-06 sampling, support counting, and asymptotic bridges: independent review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026.
**Scope:** `GraphSampling.lean`, `GraphSupportCount.lean`, `Bernoulli.lean`,
and the updated `Asymptotic.lean` at the exact SHA-256 hashes below, compared
with the frozen `NLA.Statements.RA06.Target`, the canonical RA-06 README,
the numerical specification, and the source manuscript. I did not edit
proof source. **Verdict:** the stated intermediate theorems are mathematically
aligned with their explicit hypotheses and pass a
local LeanCert kernel audit. They do **not** prove the full RA-06 Target.

## Exact target and sampling interface

The canonical problem fixes an arbitrary real `p>2` and asks for positive
`C_p,c_p`, chosen before `n,d,A,ε,δ`, such that one **same** `α>0` gives both
the expected-size budget and success probability at least `1−δ` for every
full-column-rank matrix. Its row scores are the ordinary all-nonzero-vector
sensitivities; its independent Bernoulli probabilities are exactly
`q_i=min(1,1/n+s_i/α)`. A successful outcome preserves both `p`-energy
inequalities for **all** real vectors simultaneously. The frozen Target is
`∀ p : ℝ, 2<p → ¬ OriginalPositiveClaim p`, with the original quantifier
order and the raw logarithm `log(2*n*d/(ε*δ))^c`. The canonical README's
Solved resolution states this full negation. These four reviewed modules do
not redefine `Target`, the probabilities, or the event.

`GraphSampling.lean` has the following exact bridge signatures (with
`n=card (Edge (d+1))`, `A=GraphMatrix d`, and a Boolean `kept : Fin n→Bool`):

- `SampleWeight d p α kept e` is **exactly** `1/q_i` when the edge's indexed
  row is retained, and zero otherwise. `sampleWeight_nonneg` derives
  `0≤SampleWeight` from `d>0` and `α>0`, using the actual full-rank grounded
  graph matrix and the frozen floor/cap probability. It makes no assumption
  of equal sensitivities or a common retention probability.
- `sampledEnergy_eq_weighted` proves an **equality** between the frozen
  `SampledEnergy (GraphMatrix d) p α kept x` and the graph's
  `WeightedEnergy p (SampleWeight d p α kept) (GroundPotential x)`.
  `Fintype.sum_equiv (edgeIndex d)` preserves every edge and every reciprocal
  weight, without a numerical approximation. The equality is algebraic even
  outside admissible `α`; the later use of `α>0` guarantees each reciprocal
  really is the target's positive `1/q_i`.
- The four shift lemmas show that replacing any graph potential `z` by
  `z_j−z_0`, with vertex zero grounded, leaves each edge difference, the
  complete energy, and the weighted energy unchanged. `embedding_to_weighted`
  therefore transports an `Embedding (GraphMatrix d) p α ε kept` to both
  inequalities for **every** `z : Fin (d+1)→ℝ`, with the same `kept`, `α`,
  `p`, and `ε`. This includes potentials selected after observing the support;
  the theorem does not replace the simultaneous event by a per-vector event.

This bridge is faithful to the original matrix sampler, but says nothing yet
about the probability or support size of a successful outcome. It does not
assert the manuscript's equal-sensitivity identity or common `q`.

The decisive `GraphSampling` conclusions, copied from the source with their
universal binders, are:

```lean
sampledEnergy_eq_weighted (d : ℕ) (p α : ℝ)
    (kept : Fin (Fintype.card (Edge (d + 1))) → Bool)
    (x : Fin d → ℝ) :
  SampledEnergy (GraphMatrix d) p α kept x =
    WeightedEnergy p (SampleWeight d p α kept) (GroundPotential x)

embedding_to_weighted (d : ℕ) (p α ε : ℝ)
    (kept : Fin (Fintype.card (Edge (d + 1))) → Bool)
    (h : Embedding (GraphMatrix d) p α ε kept) :
  ∀ z : Fin (d + 1) → ℝ,
    (1 - ε) * CompleteEnergy p z ≤
      WeightedEnergy p (SampleWeight d p α kept) z ∧
    WeightedEnergy p (SampleWeight d p α kept) z ≤
      (1 + ε) * CompleteEnergy p z
```

## Exact support count and Bernoulli expectation

`GraphSupportCount.lean` proves `sampleWeight_positive_iff`: for `d>0` and
`α>0`, a graph edge has positive weight **if and only if** its corresponding
Boolean row was retained. This uses the target's strictly positive `q_i`;
there is no extra common-probability hypothesis. Hence
`sample_positiveEdgeCount_eq_retainedCount` identifies the graph's number
of positive edges with the target sample's exact realized row count. The
finite-bijection proof checks the `edgeIndex` orientation and counts each
edge once. The module also proves the weighted-support handshake identity
`∑_u SupportDegree w u = 2*PositiveEdgeCount w` for any real edge-weight
function `w`: both sides count only edges with `0<w e`.
`positiveEdgeCount_lower_of_all_degrees` is the exact real consequence
`v*T ≤ 2*PositiveEdgeCount w` if `T≤SupportDegree w u` for every vertex.
It does not yet establish the needed lower bound on each degree.

`Bernoulli.lean` expands the **frozen independent product** outcome law and
proves `expectedSize_eq_sum_count`:

```lean
ExpectedSize A p α =
  ∑ kept : Fin n → Bool,
    OutcomeWeight A p α kept * (RetainedCount kept : ℝ)
```

The private marginal calculation works for unequal `q_i` and uses no
asymptotic or sampling approximation. Its
`expectedSize_lower_of_success_count_bound` assumes full column rank,
`n,d>0`, `α>0`, and a fixed lower bound `L≤RetainedCount kept` for **each**
outcome satisfying the frozen all-vector `Embedding`. It concludes

```lean
SuccessProbability A p α ε * L ≤ ExpectedSize A p α.
```

The proof sums nonnegative exact outcome masses; it does not replace a
success event by a mean-event or discard the probability factor. Combining
this with the Target's `1−δ≤SuccessProbability` would require `0≤L` and
gives `(1−δ)*L≤ExpectedSize`, the necessary factor for the arbitrary-weight
support route. That final combination and the sample-specific all-success
lower bound are not yet present.

## Numerical and asymptotic scope

`Asymptotic.lean` retains four source-coefficient lemmas using
`K=2^(p−2)+1` and `L=6^(−p)/3`. In particular,
`exists_large_accuracy_parameter` gives `b≥3` and the strict inequality

```text
C*K*log(32*b^(3*p+7))^c < L*b^(p−2).
```

The old coefficient pair matches the manuscript's common-probability
expected-size obstruction, but the presently proved `GraphMatrix.lean`
sensitivity upper bound is only `K=2^p+1`. Thus the old finite contradiction
cannot be instantiated from current graph lemmas without an additional
sharper sensitivity theorem. The updated module instead proves
`exists_large_accuracy_parameter_for_coefficients` and
`finite_bounds_contradict_for_coefficients` for **any** positive `K,L`.
The latter explicitly assumes, for the same real `v,S,E`,

```text
S ≤ K*v,
L*v*b^p ≤ E,
E ≤ C*b^2*S*log(32*b^(3*p+7))^c,
C*K*log(32*b^(3*p+7))^c < L*b^(p−2).
```

It then derives `False` by the exact identity `b^p=b^(p−2)*b²`. Here a valid
future instantiation with natural vertex count `v` and `d=v−1` may use
`S=TotalSensitivity (GraphMatrix d) p + d`,
`E=ExpectedSize (GraphMatrix d) p α`, `K=2^p+1`, and (if the arbitrary-weight
support theorem is proved) `L=(1−δ)*6^(−p)/2=3*6^(−p)/8` at `δ=1/4`.
**The factor `1−δ` must remain** on this support-expectation route; positive
success alone cannot transfer a realized support lower bound to the
expectation. The generic lemmas permit this coefficient without silently
using the stronger common-probability conclusion.

The exact generic numerical interfaces are
`exists_large_accuracy_parameter_for_coefficients`, which assumes
`2<p`, `0<C`, `0<c`, `0<L`, `0<K` and returns a natural `b≥3` satisfying
`C*K*log(32*b^(3*p+7))^c < L*b^(p−2)`, and
`finite_bounds_contradict_for_coefficients`, which assumes `2<p`, `0<C`,
`0<L`, `0<K`, `b≥3`, `0<v`, and all four displayed inequalities before
returning `False`. In the latter theorem `c` has no positivity premise;
the separation theorem supplies that premise at its point of use.

The log lemmas prove an upper bound with the original numerical choices
`ε=1/b`, `δ=1/4`, and `v=ceil(b^(p+2))`. In particular,
`budget_log_upper_for_ceiling_card_bound` proves

```text
log(2*n*(v−1)/((1/b)*(1/4))) ≤ log(32*b^(3*p+7))
```

for `b≥3`, `p>2`, `n>0`, and `n≤v*v`. This is a coarse edge-cardinality
interface that can be instantiated by `n=card(Edge v)` once that cardinality
bound is supplied. `completeGraph_budget_log_upper_for_ceiling` proves the
corresponding exact binomial-count form, while
`completeGraph_log_upper_of_ceiling_bound` proves the simplified real
argument `4*b*v*(v−1)^2`. All are inequalities in the safe direction and
use no floating-point calculation. A future final proof must still apply
monotonicity of nonnegative-base real power with `c>0` to transfer this log
bound into the raw expected-size budget.

`accuracy_parameter_dimension_regime` proves
`6^(−p)*b^(p+1)+1 ≤ b^(p+2)` for real `b≥3`, the numerical regime needed
for the manuscript's graph support obstruction. Converting this, the ceiling
choice, and natural vertex count into the exact finite support theorem is
outside the reviewed module. The logarithmic exponent `c` is assumed
positive in the existence theorem; the conditional contradiction does not
need that assumption after the strict separation and nonnegative log power
have been supplied.

## Reproducible kernel check and proof escape scan

The statement project pins Lean `v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. With that Lean binary
first on `PATH`, I ran from `lean-statements`:

```sh
lake build NLA.Proofs.RA06.GraphSampling NLA.Proofs.RA06.Asymptotic
lake env lean NLA/Proofs/RA06/GraphSampling.lean
lake env lean NLA/Proofs/RA06/Asymptotic.lean
lake env lean /private/tmp/ra06-sampling-asymptotic-audit.lean
lake build NLA.Proofs.RA06.GraphSupportCount NLA.Proofs.RA06.Bernoulli
lake env lean NLA/Proofs/RA06/GraphSupportCount.lean
lake env lean NLA/Proofs/RA06/Bernoulli.lean
lake env lean /private/tmp/ra06-supportcount-bernoulli-audit.lean
```

All exited zero. The first Lake command completed 2,061 jobs; the second
completed 2,060 jobs. All four direct `lean` calls freshly elaborated the
source. The first temporary audit imports `GraphSampling` and `Asymptotic` and
`LeanCert.Tactic.Verification`, sets `leancert.trust "kernel"`, and runs
`#assert_trust kernel` on all seven `GraphSampling` theorems and all eleven
`Asymptotic` theorems. The second temporary audit does the same for the eight
public `GraphSupportCount` theorems and two public `Bernoulli` theorems. The
audits also print axioms for principal exports; those outputs, as well as the
modules' own `#print axioms` outputs, contain only
`[propext, Classical.choice, Quot.sound]`. The four reviewed source
files contain no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, or
`native_decide`; the direct dependency chain's previously reviewed graph
lemmas has the same standard-axiom audit. This certifies the particular
conditional theorems, not the frozen `Target`: its own `#assert_trust kernel`
checks a **statement definition**, not a proof of the proposition.

There is no isolated Linux Comparator acceptance for RA-06 and no theorem
inhabiting `NLA.Statements.RA06.Target` at these hashes. The remaining
mathematical bridge is to prove the arbitrary-nonnegative-weight finite
support obstruction for **each successful outcome**, use the now-proved
retained-edge and Bernoulli identities to obtain its expected-size lower
bound with the success factor, instantiate the graph cardinality and ceiling
bounds, and combine the
original positive claim's budget and success hypotheses for its same `α`.

## SHA-256 of reviewed inputs

| Repository-relative path, except the temporary audit | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-06/README.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.tex` | `21c5187b695e4469d803ceced320bd0314ade4702ed4567160f8ff835122cec7` |
| `docs/lean/statements/RA-06/NUMERICAL_TARGETS.md` | `7036e298c8f74c4693fb638daf1aa22778756a9c26c53fbc39a9341e85f3d5e8` |
| `lean-statements/NLA/Statements/RA06.lean` | `865af15803905e04de1202266f5af75fc5486b8345fdba25a44052202742883d` |
| `lean-statements/NLA/Proofs/RA06/GraphSampling.lean` | `0f94b12262f18313b607907fe2f9aeb2d071fb7901d0f56a8e21e97085610e8a` |
| `lean-statements/NLA/Proofs/RA06/GraphSupportCount.lean` | `2447bf20d910f2393a5317d4c1a7c63696a522aef9b91d8fbb7df1abc779f87b` |
| `lean-statements/NLA/Proofs/RA06/Bernoulli.lean` | `5da1edcb106c85ea14255b2b975f137a1ed39b0c7332088c8b15170b8b33d5b4` |
| `lean-statements/NLA/Proofs/RA06/Asymptotic.lean` | `4d39acee6e037a457445f6908bc16c82a40bed299fd15061f6df92eb7fe5d8f1` |
| `lean-statements/NLA/Proofs/RA06/GraphMatrix.lean` | `aed5d4d668004e1b03ad6b98e73db1573d6fa9743a93f0cf34fc1b4c813e28ec` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `/private/tmp/ra06-sampling-asymptotic-audit.lean` | `cb79f317e0fcc456896bb81b433fdc1ec7b275c2998e1ebf0db6c167445189dd` |
| `/private/tmp/ra06-supportcount-bernoulli-audit.lean` | `c0157797e4511735d08fb79a32ebb210f0074985a82062612a3cc9618e197c9f` |
