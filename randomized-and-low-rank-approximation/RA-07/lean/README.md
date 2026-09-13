# RA-07 Lean formalization

The complete original discrete-convexity theorem is **Lean verified** as of
12 September 2026. Its unchanged proof at
[revision bf144a8](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/bf144a8ea84992d64f79f4425b18352843376286/randomized-and-low-rank-approximation/RA-07/lean)
passed two independent statement reviews, two independent final proof reviews,
and actual sandboxed Linux Comparator/default-kernel verification in
[run 34715563781](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34715563781).
The [independent operational audit and original artifacts](verification/linux-2026-09-12/)
bind all six exports and the complete 123-file verified input set.

Formalization: **George Stepaniants**, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
Mathematical proof: **Matthew J. Colbrook**, Department of Applied Mathematics
and Theoretical Physics, University of Cambridge. This is AI-assisted work with
independent agent reviews; no external human peer review or source-author
endorsement is claimed.

## Exact mathematical scope

For every `n ≥ 3`, every strictly positive real tuple `lam : Fin n → ℝ`, and
every original index `2 ≤ j ≤ n−1`, the proof establishes

```math
F_{j-1}-2F_j+F_{j+1}\geq0,
\qquad F_j=(j+1)e_{j+1}/e_j.
```

Here `e_j` is the actual sum of products over all subsets of cardinality `j`.
The proof derives the empty-subset value, oversized values and denominator
positivity. It includes repeated entries, equal spectra, dimension three and
the final index where `F_n=0`. No ordering, normalization, bounded spectrum,
assumed factorization or generic-position condition is imposed.

The [canonical question](../README.md) and Colbrook's
[complete Theorem 1.1 and source proof](../../../references/colbrook-transfer-2026-09-11/manuscripts/01_volume_sampling_convexity.tex)
are retained at source revision
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. The manuscript's strict monotonicity,
extra index-one assertion, volume-sampling expectation identity, Jensen
application and stable-rank bounds are outside the six formal exports.
The scalar convexity assertion above is the complete original target.

## Proof and selected exports

[Definitions](NLA/RA07/Definitions.lean) use genuine finite subset sums and
actual polynomial derivatives. [Algebra](NLA/RA07/Algebra.lean) identifies
the generating coefficients and factorial-scaled derivative values.
[Roots](NLA/RA07/Roots.lean) proves exact derivative degree and uses Mathlib's
Gauss–Lucas theorem to obtain strictly negative real roots, then derives real
splitting and a factorization containing every root with its multiplicity.
This includes the final constant derivative with an empty factor tuple.
[Sums](NLA/RA07/Sums.lean) proves the exact finite-product derivative and
unordered-pair identities. [Proof](NLA/RA07/Proof.lean) transfers those
identities to the actual original ratios.

At index `j`, the actual derivative of order `j−1` has
`n−(j−1) ≥ 2` positive reciprocal-root factors `μ`. The resulting certificate is

```math
F_{j-1}-2F_j+F_{j+1}
=\frac{2\sum_{a<b}\mu_a\mu_b(\mu_a-\mu_b)^2}
{s_1(s_1^2-s_2)},\qquad s_r=\sum_a\mu_a^r.
```

The denominator is proved strictly positive using
`s₁²−s₂ = 2∑(a<b) μₐμ_b`; the numerator is nonnegative. No numerical root
finding, interval subdivision or approximate spectrum is used.

All declarations below have prefix `NLA.RA07.`. Their complete statements are
in [Challenge](Challenge.lean), and their completed proofs are exported from
[Solution](Solution.lean). [Comparator](comparator.json) selects all six,
with empty `definition_names` and only the three standard permitted axioms.

| Declaration | Scope |
| --- | --- |
| `elementary_values` | Actual endpoint conventions and positivity of elementary sums. |
| `generating_derivative_values` | Coefficients and actual derivative values, including factorials. |
| `positive_derivative_factorization` | Exact degree and full-multiplicity factorization of every relevant actual derivative. |
| `power_sum_certificate` | Positive denominator and nonnegative exact pair identity. |
| `second_difference_certificate` | Exact certificate for every original index and the actual sequence. |
| `errorSequence_convex` | Complete affirmative canonical theorem. |

## Trust and completed reviews

The project pins Lean **4.33.1**, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`.
Proof and Solution explicitly select `leancert.trust "kernel"`.
LeanCert is used for **kernel trust auditing of exact algebra and root
geometry**. There is no interval calculation or claimed numerical LeanCert
certificate in this project. The twelve distinct internal/public source
assertions and their transitive axiom reports passed with exactly
`propext`, `Classical.choice`, and `Quot.sound`.

There are no implementation or definition proof holes. The six deliberate
Challenge placeholders are isolated statements and are excluded from the
manifest's proof-development sorry counts; Solution does not import Challenge.

- Statement reviews: [referee 1](reviews/statement-referee-1.md) and
  [referee 2](reviews/statement-referee-2.md), both before implementation.
- Final proof reviews: [referee 1](reviews/proof-referee-1.md) and
  [referee 2](reviews/proof-referee-2.md), both independent of the implementer.
- [Proof completion](reviews/proof-completion.md),
  [frozen proof hashes](verification/proof-freeze.json),
  [author's fresh check](verification/fresh-checks.json),
  [first referee evidence](verification/final-referee-1/evidence-manifest.json)
  and [second referee evidence](reviews/proof-referee-2-root-evidence/manifest.json).
- [Exact numerical targets](NUMERICAL_TARGETS.md),
  [source correspondence](SOURCE_MAP.md) and
  [v0.4 formalization metadata](formalization.yaml).

The local referee checks used fresh target artifacts on macOS and matching
dependency caches at ten verified clean pins. The later authoritative Linux run
cloned all ten dependencies at their exact revisions and downloaded/decompressed
8690 official Mathlib cache files before building the RA-07 sources. No user
project build cache was reused; this is not a claim that every dependency module
was rebuilt from source. The relevant
[pinned referee standards](../../../docs/lean/REVIEW.md) were adapted to the
complete original scope and actual mathematical definitions.

## Reproduction and actual Linux evidence

From this project directory, with its pinned toolchain and dependencies:

```
lake exe cache get
lake build NLA.RA07.Proof Solution Challenge
lake env lean Solution.lean
```

The explicit targets include the completed proof; the package's preserved
default target is its statement Challenge. Compilation is a local check.
The repository's [shared Linux workflow](../../../docs/lean/README.md) built
and exported both environments, compared all six statements, replayed the
solution in Lean's default kernel, and ran the real isolation/rejection controls.
From the immutable verified revision on a correctly configured non-root Linux
host, run these shared commands from the repository root:

```
./tools/lean/bootstrap.sh /tmp/nla-ra07-tools
./tools/lean/selftest.sh /tmp/nla-ra07-tools
./tools/lean/verify.sh \
  randomized-and-low-rank-approximation/RA-07/lean \
  /tmp/nla-ra07-tools
```

The actual RA-07 job and the separate checker job both passed. Their original
ZIPs, raw logs, complete verified sources, exact input/tool hashes and independent
audit are retained in [the Linux evidence directory](verification/linux-2026-09-12/),
bound by its [evidence manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json).
The operational report distinguishes the observed controls precisely: the nested
bubblewrap executable ran, but UID-map creation was denied before its inner write.
No general sandbox-security guarantee is inferred from those finite controls.

Historical statement/proof records retain their original phase labels and
hashes. The exact old statement-stage README is retained in
[the candidate evidence](verification/linux-candidate-2026-09-12/frozen-statement-stage-README.md).
The original candidate had changed only its current README among the 38
proof-freeze inputs. Publication now changes only this README and the current
formalization manifest among the 123 Linux-verified inputs; all other 121,
including every mathematical file, configuration, pin and prior review, remain
byte-identical. All 239 retained Linux evidence files are unchanged. Their source
snapshots retain the then-pending metadata: the successful run is bound to the
immutable proof revision and is not represented as a new run over these updated
publication wrappers. The canonical original target and Colbrook source files
remain unchanged.

The [publication evidence supplement](verification/publication-2026-09-12/evidence-count-supplement.json) records the exact 239-file retention count. The original outer manifest binds 237 files; its own file and one nested source manifest complete the total. The nested manifest is already hash-bound by the actual Linux input receipt, and its bytes are additionally recorded in the supplement. The original operational audit and outer manifest remain unchanged.
