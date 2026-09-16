# IE-14: sharp growth for complex cyclic tridiagonal partial pivoting

**Stage: complete local proof candidate.** All seven reviewed declarations build
in `Solution` with explicit kernel-trust assertions and only the three permitted
axioms. Both exact-byte pre-proof statement reviews approved the ten boundary
inputs, committed at `58b516b6dbb7fa4e885b679d261bf779c263aad4` before proof
implementation. Independent complete-source reviews and authoritative Linux
Comparator/default-kernel verification are pending. Canonical status remains
**Solved**.

**Formalization:** George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with substantial OpenAI Codex
assistance. **Original mathematical resolution:** Matthew J. Colbrook, Department
of Applied Mathematics and Theoretical Physics, University of Cambridge.
The complete [canonical statement](../README.md),
[original manuscript](../../../references/colbrook-recovered-2026-09-11/manuscripts/IE-14.tex),
[PDF](../../../references/colbrook-recovered-2026-09-11/manuscripts/IE-14.pdf), and
[historical review](../../../references/colbrook-recovered-2026-09-11/verification/reviews/IE-14-review.md)
are preserved. No contact email is introduced. No author endorsement or external
human review is claimed by this formalization.

## Complete mathematical scope

For every `n≥4`, the sharp growth factor is `Nat.fib (n+1)+1`, with Fibonacci
convention `F₀=0,F₁=1`. Inputs are all nonsingular **complex** cyclic tridiagonal
matrices with both corners nonzero. Every largest-modulus partial-pivoting tie
choice and every entry of every active Schur complement are included. No symmetry,
real-entry, diagonal-dominance or genericity assumption is added.

The original row and column ordering is fixed at the start. Definitions implement
literal row swaps and exact Schur updates, padded by zero outside the active block.
The finite maxima use actual complex entry moduli. The numerator includes the
input and final scalar, so the result controls the whole active history.

The all-size rational witness has entry maximum one and follows the explicit
physical path that keeps the first row, then selects the current last row at
every later stage. The construction assigns the input rows of `L U`; a separate
trajectory theorem proves that the subsequent legal GEPP swaps realize the
intended original-row order `(1,n,2,…,n−1)`. This row assignment is not an initial
permutation applied to the input run.

`IsGreatest` proves actual attainment, nonemptiness and the universal upper bound
before the real-supremum equality. A separate semantic theorem proves existence
of a complete admissible path for every nonsingular complex square matrix,
without a cyclic-pattern or positive-dimension restriction.

The [reviewed dossier](NUMERICAL_TARGETS.md) records all seven statements, exact
source hashes and proof obligations. The frozen [Comparator configuration](comparator.json)
allows no replaceable definition holes. [formalization.yaml](formalization.yaml)
records this local candidate's scope, attribution, exports and pending gates.

## Proof structure and computation

The `NLA/IE14` package contains twelve modules, including the frozen definitions.

| Modules | Mathematical content |
| --- | --- |
| `Definitions` | Literal complex GEPP, admissible ties, finite entry/active maxima, the growth-value set, real supremum, and all-size rational witness/path. |
| `Basic`, `GEPP` | Finite maximum semantics and complex multiplier bounds. Injectivity on vectors supported in the true active block is preserved through swaps and Schur steps, yielding nonzero pivot columns and a complete path. No determinant-nonzero assertion is made for the zero-padded whole matrix after elimination. |
| `Certificates` | Explicit LeanCert kernel certificates `0 < (1/2 : ℝ)` and `(1/2 : ℝ) ≤ 1`. |
| `Front` | The permutation of original row labels and a recursively updated pair of old physical row positions. Every later original row stays active and unchanged until entering the front. Every admissible nonzero pivot lies in the two-old/one-fresh front. |
| `FrontBounds`, `ColumnBounds` | Complex modulus estimates for each of the three possible removed rows. The old pair's maximum and sum satisfy symbolic Fibonacci recurrences. Separate histories cover the first, second, middle, penultimate and last columns, with the `n=4` boundary and final two-row step included. |
| `Factors`, `Tail`, `WitnessEntries` | Triangular determinant/nonzero-pivot facts, all structural zeros, both actual corners and exact entry maximum one. A tail-product identity in physical row positions proves the literal current-last-row path, every selected pivot's maximality and the final scalar. |
| `Attainment`, `Proof` | The universal entry bound yields growth control; the witness attains the bound. The exact greatest-value and real-supremum conclusions follow, and the seven public closures receive kernel/axiom checks. |

The scalar front bookkeeping records a pair maximum `M` and sum `T`, avoiding
a sorted-row construction. With a zero fresh target entry, `M′≤T` and `T′≤T+M`;
with a fresh target modulus at most `c`, `M′≤max(T,M+c)` and
`T′≤T+c+max(M,c)`. These consequences hold for every permitted pivot choice and
retain the source's complete column bounds.

Both numerical certificate components are genuinely consumed. Strict positivity
passes through `half_complex_ne_zero` into nonzero upper-factor pivots and witness
nonsingularity/path legality. The upper bound passes through
`norm_half_complex_le_one` into the exact input-entry maximum. The certificate is
therefore on the final witness's dependency path. The dimensions, complex front,
Fibonacci recurrence, triangular determinant and actual trajectory are proved
symbolically; finite computations do not replace these arguments.

## Exported results

All declarations are in namespace `NLA.IE14` and match the seven independently
reviewed Challenge targets.

| Declaration | Exact role |
| --- | --- |
| `numerical_bounds` | Consumed kernel-certified conjunction `0 < (1/2 : ℝ)` and `(1/2 : ℝ) ≤ 1`. |
| `entryMax_semantics` | Nonnegativity, universal entry bound and actual attainment of the finite maximum for every `n≥1`. |
| `admissible_path_exists` | A complete genuine GEPP path for every nonsingular complex square matrix. |
| `all_active_entries_bound` | Every active entry, on every permitted path of every canonical input, is bounded by `(F_(n+1)+1) * entryMax A`. |
| `witness_data` | The exact all-size witness is nonsingular, has the full cyclic pattern and both corners, and has entry maximum one. |
| `witness_attainment` | The actual specified physical path is admissible and its full growth equals `F_(n+1)+1`. |
| `canonical_result` | The growth-value set has greatest element `F_(n+1)+1`, and its real supremum equals that value, for every `n≥4`. |

`entryMax_semantics` is implemented directly in `Basic.lean`; the other six public
declarations are in `Proof.lean`.

## Reproduction and evidence

Run Python commands in an environment with the dependencies from
[tools/lean/requirements.txt](../../../tools/lean/requirements.txt).

```bash
lake exe cache get
lake build Challenge
lake build Solution
python3 ../../../tools/lean/validate_manifest.py .
python3 reviews/initial/exact-check.py > /tmp/ie14-exact-results.json
cmp reviews/initial/exact-results.json /tmp/ie14-exact-results.json
```

Pins: Lean **4.33.1**, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`.
The default Lake target remains the frozen Challenge. Its seven intentional
specification placeholders establish no theorem and are excluded from the zero
proof-development sorry counts. `Solution` imports the implemented proofs and
does not import Challenge.

The [local Solution build log](verification/local-solution-build.log) records
successful kernel-trust assertions and axiom checks for all seven target closures.
It is local contributor evidence; it is not independent final review, actual
Comparator correspondence, or isolated Linux verification.

The portable standard-library Fraction diagnostics check all 27 rational witnesses
for `4≤n≤30`, including the literal current-last-row swaps, every active entry,
nonzero/maximal pivots, exact tail-product identities and recorded growth. They
also check the preserved source hashes. These finite diagnostics are not a proof
of the universal result or the all-size witness.

## Independent review and remaining gates

The [statement freeze](reviews/statement-freeze.json) retains all ten approved
input hashes and both sealed statement reports:
[referee 1](reviews/statement-referee-1.md) and
[referee 2](reviews/statement-referee-2.md). Those inputs remain unchanged. The two
referees contributed no proof code.

The repository [review protocol](../../../docs/lean/REVIEW.md) applies Tau Ceti
referee standards through independent AI-agent reviews. Complete-source reviews
and the [Linux harness](../../../tools/lean/HARNESS.md) remain pending. Promotion
requires actual pinned Lean4 Comparator, default-kernel replay, transitive
permitted-axiom checks, real sandbox probes, rejection controls and independent
operational review. No **Lean verified** status is asserted at this stage.

The pinned [Forsythe](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof)
and [Schiffer](https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1)
projects supply structure/API references. The existing IE-05/IE-15 developments
inform finite-maximum, supported-vector injectivity and trailing-sum proof
patterns; their real or rook-pivoting theorems are not assumed to cover complex
GEPP. No official Tau Ceti endorsement, external human review, novelty
certification or unmeasured proof-cost claim is made.
