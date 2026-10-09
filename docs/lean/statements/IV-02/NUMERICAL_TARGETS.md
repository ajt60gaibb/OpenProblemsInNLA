# IV-02 — exact mathematical and numerical specification

## Review and implementation state

Preimplementation specification authored by OpenAI Codex AI agent
`/root/inventory` on 2026-09-28. Two independent approvals are required before
implementation. No Lean target or proof is supplied by this document. The
canonical status **Solved** records the existing complexity classification;
it does not assert an unconditional polynomial algorithm or a formal proof.

## Frozen canonical identity

- Permanent ID: `IV-02`.
- Canonical README: `intervals-and-absolute-value-equations/IV-02/README.md`.
- Campaign base revision: `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.
- Complete original: `ORIGINAL.md`, byte-for-byte equal to the canonical README,
  including the resolution, source references and every historical audit.
- Canonical README SHA-256: `8b1ffc82e9760aaffee717005e4547dc9cace7f97bc77d0f0f82a25b62b303d7`.
- `source-lock.json` binds the README, LaTeX problem, archived joint manuscript,
  and the historical local Challenge/Reduction/Solution/SPEC sources.

The canonical ID, path, complete source, and original mathematical question
remain unchanged. The target excerpt below is verbatim; the complete original
and all recorded source hashes govern any apparent discrepancy.

## Exact mathematical target and quantifier order

For every `n≥2`, an input consists of `n` diagonal, `n-1` upper-diagonal,
and `n-1` lower-diagonal closed intervals with ordered rational endpoints.
Let `𝒯(I)` contain **all real** `n×n` matrices whose corresponding entries
belong to those intervals and whose other entries are zero. The entry choices
are mutually independent. Do not restrict admissible matrices to rational
entries or require nonsingularity.

For rational numbers `dlo,dhi`, define `CorrectRange I dlo dhi` by all of:

1. Every `T∈𝒯(I)` satisfies `(dlo:ℝ) ≤ det T ≤ (dhi:ℝ)`.
2. There exists `Tlo∈𝒯(I)` with `det Tlo = (dlo:ℝ)`.
3. There exists `Thi∈𝒯(I)` with `det Thi = (dhi:ℝ)`.

The two matrices may differ. These clauses are the exact minimum and maximum,
not merely an enclosure or an interval containing all endpoint determinants.
Multiaffinity and compactness explain why such rational extrema exist; no
proof of those facts is required just to define their requested semantics.

The original question becomes the following closed proposition:

```text
Target := ∃ M : FiniteMachine, ∃ p : PolynomialBound,
  ∀ n ≥ 2, ∀ valid tridiagonal interval input I of dimension n,
    ∃ dlo dhi : ℚ,
      M.RunsWithin (encodeInput I) (encodeRange dlo dhi)
        (p.atLength (encodeInput I).length)
      ∧ CorrectRange I dlo dhi.
```

The output word is exactly `encodeRat dlo ++ encodeRat dhi`, in that order,
with no extra symbols. The run must halt. All input instances, including zero
width intervals, intervals crossing zero, and families containing singular
matrices, are included. The existence of mathematical extrema without this
single uniformly bounded machine is insufficient.

## Published classification and scope of the statement

The original problem asks whether `Target` holds. Preserve that question even
though the canonical resolution classifies its complexity. Do not negate
`Target` on the assumption `P≠NP`, and do not assume `P=NP` to manufacture an
affirmative answer. If a separate credited classification is later formalized,
its form is `Target ↔ PEqualsNP`, where
`PEqualsNP := ∀ L : Set Word, Complexity.InP L ↔ Complexity.InNP L` uses the
reviewed concrete finite-machine classes. This is a separate proposition;
`Target ∧ (Target ↔ PEqualsNP)` would wrongly assert the original affirmative
answer as part of the resolved classification. The campaign's required
`NLA.Statements.IV02.Target` denotes the original algorithm-existence question.

The archived joint manuscript's Theorem 1 classifies the upper-determinant
threshold as NP-complete and the exact range as NP-hard, even for regular
families with fixed superdiagonal entries one. Section 5 proves the full
exact-output task belongs to `FP^NP` by clearing a common denominator `D`,
bounding integer determinants by `n! H^n`, binary searching NP threshold
queries, then dividing by `D^n`. These are credited proof obligations, not
assumed oracles or alternate definitions of the target. No claim of strong
NP-hardness or unconditional separation appears here.

## Historical Lean gap to be repaired

The locked historical `lean/Challenge.lean` correctly describes rational
interval data, real admissible tridiagonal matrices and attained determinant
bounds. Its `ComplexityContract`, however, has four arbitrary `Prop` fields;
`thresholdProblem` only existentially chooses a contract whose fields hold.
Every field can be instantiated by `True`, so this formula expresses no NP
membership, hardness, running time, or algorithm. Its final `IV02Statement`
conjoins that formula with pointwise existence of exact ranges, which drops
the central uniform polynomial computation question.

The historical reduction/support proves rational rotation identities and a
layer-count fact. Those useful facts do not restore the missing finite-machine,
encoding, complexity-class, or reduction semantics. Keep all historical files;
the new statement uses the reviewed concrete machine execution instead of the
arbitrary `Prop` contract. A later proof of the claimed classification will
also need actual reductions and upper-bound algorithms, but those are not
prerequisites for defining the faithful original question.

## Exact binary computation boundary

Use the already reviewed `NLA.Computation.FiniteMachine`, `PolynomialBound`,
and canonical natural/integer/rational encoders in `BinaryEncoding`. A machine
has a finite control table over the fixed blank/zero/one tape alphabet. Its
`RunsWithin w v T` means an actual initial-to-halting tape execution taking at
most `T` move/write transitions, with exactly the complete output word `v` on
the final tape suffix. There is no arbitrary evaluator, unit-cost rational or
real arithmetic, supplied polynomial-time oracle, or assumed algorithm.

Choose the machine and one bound `C*(length(w)+1)^k` before all dimensions and
inputs, with natural `C>0` and natural `k`. The complete input word, including
all dimension, numerator and denominator bits and framing, is counted. The
same transducer must work on every valid input, not one machine per dimension
or instance. No promise recognition is required beyond the stated rational
interval input conditions; behavior on malformed words is unrestricted.

The compact tridiagonal input encoder is fixed as follows. Encode `n`, then
all `n` diagonal intervals in increasing index order, then the `n-1` upper
intervals, then the `n-1` lower intervals, again in increasing index order.
An interval is `encodeRat lower ++ encodeRat upper`; all rationals use the
reviewed canonical reduced signed-numerator/positive-denominator representation.
No off-band entries are transmitted: they are identically zero. Each occurrence
is independent, even when two intervals happen to have equal endpoints. Zero
width intervals are allowed. Validity means each lower endpoint is at most its
upper endpoint and the problem's dimension restriction holds. Proof fields do
not contribute bits. Do not encode a general dense interval matrix while
silently counting only its tridiagonal entries.

A new shared helper module may define this compact band data, its explicit
encoder, and its real-matrix membership relation. This requires definitions,
not a determinant, LP, or exact-output algorithm. General codec correctness and
polynomial equivalence with other conventional binary encodings are later
proof obligations; they must not be asserted as assumptions in `Target`.
The encoding itself must be explicit and independently reviewed, so its
syntactic choice cannot identify distinct mathematical inputs.

## Numerical work and verification boundary

No numerical certificate or large finite enumeration is needed to state the
problem. Exact rational endpoints, ordinary real matrix operations, and actual
bounded machine runs are sufficient. Do not replace all inputs by sampled
matrices, positive intervals, regular families, a fixed dimension, or an
exponentially enumerated algorithm with a fictional polynomial cost.

The Lean artifact is a closed proposition, not a proof of that proposition.
Type checking, kernel axiom auditing and frozen Comparator identity establish
only their stated mechanical boundaries. Two independent mathematical reviews
of these exact bytes are required before implementation; two independent
reviews of the final Lean definitions and full import closure are required
afterward. If later numerical certificates are introduced, the shared pinned
LeanCert dependency must use `set_option leancert.trust "kernel"`, explicit
`leancert (trust := kernel)` and `#assert_trust kernel` for exported results.
Purely symbolic statements require no artificial numerical computation.

## Verbatim canonical target

<!-- canonical-target-start -->
## Problem statement

For $`n\geq2`$, let the input consist of $`3n-2`$ closed real intervals with
rational endpoints: diagonal intervals $`[\underline a_i,\overline a_i]`$
for $`1\leq i\leq n`$, upper-diagonal intervals
$`[\underline b_i,\overline b_i]`$, and lower-diagonal intervals
$`[\underline c_i,\overline c_i]`$ for $`1\leq i< n`$.
All lower endpoints are at most their upper endpoints. Define

```math
\mathcal T=\{T\in\mathbb R^{n\times n}:
T_{ii}\in[\underline a_i,\overline a_i],\quad
T_{i,i+1}\in[\underline b_i,\overline b_i],\quad
T_{i+1,i}\in[\underline c_i,\overline c_i],\quad
T_{ij}=0\text{ if }|i-j|>1\}.
```

All uncertain entries vary independently. Does a deterministic algorithm
exist that returns the two exact rational numbers

```math
d_- = \min_{T\in\mathcal T}\det T,
\qquad
d_+ = \max_{T\in\mathcal T}\det T
```

in time polynomial in the total binary input length? The target is the
exact range $`[d_-,d_+]`$, including instances containing singular matrices
and intervals crossing zero. Rational output is appropriate because the
determinant is affine in each entry separately and its extrema are attained
at endpoint matrices. The polynomial bound must be uniform in $`n`$.
<!-- canonical-target-end -->
