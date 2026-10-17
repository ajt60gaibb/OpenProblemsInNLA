# SP-11 Gram and polynomial gates — independent review

Reviewer: `/root/lean_verification`, independent Codex AI agent, 17 October
2026. The reviewer did not implement these modules. **Verdict: approve the
reviewed conditional gates. No complete SP-11 proof is certified.**

The actual source and imported meanings were reviewed, then independently
compiled from frozen source copies in a fresh private output prefix with Lean
4.33.1. All ten public theorem exports passed LeanCert `#assert_trust kernel`;
each transitive axiom report is exactly `propext`, `Classical.choice`,
`Quot.sound`. All ten dependency Git pins and tracked-source cleanliness were
checked before and after compilation. No source changed during this check.

| Reviewed source under `lean-statements/` | SHA-256 |
| --- | --- |
| `NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `NLA/Statements/SP11.lean` | `7de112a24cb0b78894d495b840a77a58572cce574d5d77eda15381410c65b131` |
| `NLA/Proofs/SP11/GramBridge.lean` | `e3ff1bd936a820a58ac005dd50487464e8d5a56b231268bd1e1b5d9936ab1aed` |
| `NLA/Proofs/SP11/PolynomialFaithfulness.lean` | `e1214cdc4072420c86006538cc9465bf29e9dda5a5e72dd1a0eb9ace4fd7928c` |

The polynomial hash includes the final
`target_of_polynomial_representations` theorem added before this freeze.

## Fidelity and mathematical correctness

The frozen target quantifies over every positive `n` and every simple graph on
`Fin n`. `HasPattern` explicitly requires real symmetry and the exact
off-diagonal equivalence between nonzero entries and adjacency; the diagonal
is unrestricted. `MinimumDegree` uses Mathlib's actual finite graph minimum
degree. `Matrix.rank` is the finite-dimensional rank, so `n - A.rank` expresses
the intended nullity of a real square matrix. No connectivity, regularity,
girth, edge-weight, PSD, or SAP hypothesis was inserted into the target.

`gram` is literally `R * R.transpose`. The entry lemma expands the real dot
product. `gram_hasPattern` proves symmetry by commutativity in each summand and
uses the supplied off-diagonal iff in both directions. `gram_rank_le` applies
Mathlib's rank-of-product and width bounds; it does not assume independent
rows, full rank, or nonzero ambient dimension. The natural-number deduction
from `d + MinimumDegree G ≤ n` to `MinimumDegree G ≤ n - rank(gram R)` is
valid without replacing truncated subtraction by unjustified integer algebra.
`target_of_faithful_representations` supplies exactly the original witness
once its stated universal representation-existence premise is supplied.

For `exists_real_eval_ne_zero`, Mathlib's
`MvPolynomial.funext` is used over the infinite integral domain `ℝ`. It works
for any variable type because every polynomial has finite support. If a
nonzero polynomial vanished at every real assignment, polynomial funext would
make it zero. The simultaneous version applies this to the finite product;
the polynomial ring has no zero divisors, and evaluation is a ring homomorphism.
Thus every listed nonzero factor has a common nonvanishing assignment. The
empty-constraint case is covered by the nonzero empty product, with no
nonemptiness or genericity oracle assumed.

`eval_polynomialGram` commutes evaluation through the genuine finite sum and
products. `exists_faithful_real_evaluation` selects all diagonal and edge
polynomials at once. Its explicit `hzero` forces every nonedge Gram entry to
zero; its explicit `hnonzero` makes each edge entry nonzero. A zero evaluated
row would make its diagonal Gram entry zero, contradicting the selected
diagonal constraint, so the advertised nonzero-row conclusion is also proved.
The theorem proves neither polynomial hypothesis about an as-yet-unconstructed
Hall representation.

The final `target_of_polynomial_representations` has an explicit universal
existence hypothesis for polynomial vectors, their dimension bound, identically
zero nonedge products, and nonzero diagonal/edge products. It evaluates those
vectors and applies the Gram bound correctly. This is a proved sufficient
condition for the literal frozen target, not an unconditional theorem of that
target. The comments accurately expose the unproved witness construction and
non-cancellation obligation.

## Reuse, API, and attribution

The proof uses the existing Mathlib matrix rank and polynomial funext APIs
instead of introducing a custom rank, formal genericity assumption, or
uninterpreted polynomial evaluation. The two small Gram wrappers keep the
coordinate meaning explicit. The simultaneous-evaluation lemma is appropriately
general in variable type and finite constraint type. No numeric interval
computation is needed for these exact algebraic deductions.

The canonical original page, pre-existing SP-11 numerical specification, and
retained independent informal Hall-proof review were read. These gates match
the polynomial-specialization and final Gram/rank deductions described there.
Hall remains credited for the source mathematical result. This review does
not re-review Hall's central unique-monomial proof or certify its future Lean
implementation, and it makes no new authorship or discovery claim.

## Reproduction and limits

Run from the campaign repository root:

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-reviewed-gates.py
```

`sp11-gate-review/result.json` binds all source hashes, exact commands, Lean
version/executable digest, dependency checks, and the successful five-command
fresh build. Its source snapshots and raw logs are retained in that directory.
The independent audit consumer lists all ten exports explicitly and retains
their complete axiom output.

This is macOS source elaboration and LeanCert proof-trust evidence with trusted
compiled dependency caches. It is not authoritative Linux Comparator/exporter
or sandbox replay. The greedy construction, alternating contraction, recursive
polynomial vectors, unique-monomial non-cancellation, universal faithful-vector
existence, and complete SP-11 result are outside this review. The remaining
major premises must be proved before a full-target proof or status promotion
can be claimed. No blocking finding was identified within these reviewed
conditional modules.
