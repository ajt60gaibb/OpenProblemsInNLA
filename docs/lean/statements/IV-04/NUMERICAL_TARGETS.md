# IV-04 — exact mathematical and numerical specification

## Review and implementation state

Preimplementation specification authored by OpenAI Codex AI agent
`/root/inventory` on 2026-09-28. Two independent approvals are required before
implementation. No Lean target or proof is supplied by this document. The
canonical status **Solved** records the existing complexity classification;
it does not assert an unconditional polynomial algorithm or a formal proof.

## Frozen canonical identity

- Permanent ID: `IV-04`.
- Canonical README: `intervals-and-absolute-value-equations/IV-04/README.md`.
- Campaign base revision: `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.
- Complete original: `ORIGINAL.md`, byte-for-byte equal to the canonical README,
  including the resolution, source references and every historical audit.
- Canonical README SHA-256: `bea3f7d4322d1293944253138d3ee6f6f1fce1b1451084bfe3b6c716035c0735`.
- `source-lock.json` binds the README, LaTeX problem, archived joint manuscript,
  and the historical local Challenge/Reduction/Solution/SPEC sources.

The canonical ID, path, complete source, and original mathematical question
remain unchanged. The target excerpt below is verbatim; the complete original
and all recorded source hashes govern any apparent discrepancy.

## Exact mathematical target and quantifier order

For every `n≥1`, an input consists of the same independent tridiagonal
interval matrix data as IV-02, together with `n` independent closed right-hand
side intervals with ordered rational endpoints. There is **no regularity
promise**. Let `𝒯(I)` contain all admissible **real** matrices, let `ℬ(I)`
contain all admissible **real** vectors, and define

```text
Σ(I) := {x : Fin n → ℝ | ∃ T∈𝒯(I), ∃ b∈ℬ(I), T.mulVec x = b}.
```

All existential choices may depend on `x`. Do not replace `Σ` by rational
solutions or require an inverse. Include inconsistent singular systems,
consistent singular systems, zero-width intervals and intervals crossing zero.

An output has one global empty case or a nonempty box case. In the box case,
for each coordinate `i`, its lower endpoint is either `negativeInfinity` or
`finite q` with `q:ℚ`, and its upper endpoint is either `finite q` or
`positiveInfinity`. Using separate lower/upper endpoint types rules out
inappropriate `+∞` lower and `−∞` upper endpoints on a nonempty real set.

Define `CorrectHull I output` as follows:

- `empty` means exactly `Σ(I)=∅`.
- `box lower upper` requires `Σ(I).Nonempty` and all coordinate clauses below.
- A finite lower endpoint `q` requires
  `∀ x∈Σ(I), (q:ℝ)≤x i` and
  `∀ ε:ℝ, 0<ε → ∃ x∈Σ(I), x i < (q:ℝ)+ε`.
- A negative-infinite lower endpoint requires
  `∀ R:ℝ, ∃ x∈Σ(I), x i < R`.
- A finite upper endpoint `q` requires
  `∀ x∈Σ(I), x i≤(q:ℝ)` and
  `∀ ε:ℝ, 0<ε → ∃ x∈Σ(I), (q:ℝ)-ε < x i`.
- A positive-infinite upper endpoint requires
  `∀ R:ℝ, ∃ x∈Σ(I), R < x i`.

Thus finite endpoints are the true infimum and supremum and the infinite tags
mean genuine unboundedness. Infimum/supremum semantics use approximating
witnesses, so they require neither an undefined default for an empty set nor
an unjustified endpoint-attainment assumption. Witnesses may depend on the
coordinate, endpoint and tolerance. No common solution must realize all bounds.
The coordinate projection need not itself be an interval; its hull is the
smallest closed extended-endpoint interval containing it.

The original question becomes the following closed proposition:

```text
Target := ∃ M : FiniteMachine, ∃ p : PolynomialBound,
  ∀ n ≥ 1, ∀ valid tridiagonal interval/RHS input I of dimension n,
    ∃ output : HullOutput n,
      M.RunsWithin (encodeInput I) (encodeHull output)
        (p.atLength (encodeInput I).length)
      ∧ CorrectHull I output.
```

The existence of exact hull data independently for each input, an arbitrary
set-theoretic selection, or a bound on real arithmetic operations would not
state the required deterministic polynomial binary computation.

## Concrete output syntax and extra input fields

After the compact band encoding below, IV-04 appends the `n` RHS intervals,
in coordinate order, using the same lower-then-upper rational encoding.
There is no repeated dimension header between the matrix and RHS.

The full output word for the empty case is the single bit `[false]`.
The nonempty case is `[true] ++ encodeNat n`, followed in increasing coordinate
order by `encodeLower (lower i) ++ encodeUpper (upper i)` for each `i`.
For a lower endpoint, `[false]` means `−∞`, while `[true] ++ encodeRat q`
means the finite rational `q`. For an upper endpoint, `[false]` means `+∞`,
while `[true] ++ encodeRat q` means the finite rational `q`. The context
separates the two infinity meanings. No extra output bits are allowed. A
nonempty answer must have the original input dimension, all `n` coordinate
pairs, and exact finite rational values. The single global empty flag prevents
inconsistent coordinate-by-coordinate emptiness reports.

## Published classification and scope of the statement

Keep `NLA.Statements.IV04.Target` as the original algorithm-existence question.
The canonical **Solved** status reports a complexity classification, not an
unconditional affirmative algorithm or a proof that polynomial time is
impossible. A separately credited classification, if later formalized, is
`Target ↔ PEqualsNP`, with
`PEqualsNP := ∀ L : Set Word, Complexity.InP L ↔ Complexity.InNP L`.
It must not be conjoined with an asserted affirmative `Target` or use an
unproved assumption `P≠NP`.

The joint manuscript's Theorem 2 transfers determinant hardness to the first
hull coordinate in regular even-dimensional families with point RHS `−e_n`:
that lower endpoint equals `1/max det T`. This hard subclass does not narrow
the input space of the original target. Section 5 handles the complete scope
as a finite union of rational orthant polyhedra
`D_s x≥0`, `(C−R D_s)x≤b_c+b_r`, `(-C−R D_s)x≤−b_c+b_r`, where
`C,R,b_c,b_r` are the interval midpoints and radii. It uses NP queries for
nonemptiness, coordinate unboundedness and rational thresholds, and exact
rational reconstruction for finite endpoints. Its coefficient bound is
`Q=n! H^n` after common-denominator clearing with `H≥1`.
These arguments explain the reported `FP^NP` upper bound, finite rational
outputs, and `P=NP` equivalence. They are future proof obligations, not
assumed algorithms, oracles, or replacement semantics in this statement.
The original README discloses the empty/unbounded convention as an editorial
extension of an earlier regular-system source; this complete convention is
preserved rather than reduced back to that historical subclass.

## Historical Lean gap to be repaired

The locked historical `lean/Challenge.lean` defines real admissibility and the
united solution set, but `HullCase S` demands that the **coordinate projection
itself** equal `∅`, a finite closed interval, a closed half-line, or all of `ℝ`.
`IV04Statement` then universally asserts that shape property. General united
solution projections can be disconnected: for `n=1`, matrix interval `[-1,1]`
and RHS `{1}`, the projection is `(-∞,-1] ∪ [1,∞)`, whose exact hull is `ℝ`.
The projection is not any of the historical `HullCase` shapes. The new
infimum/supremum semantics correctly returns lower `−∞`, upper `+∞`.

The old statement also contains no concrete algorithm, binary encoding or
uniform running time. Its 2×2 inverse/corner identities in `Reduction` and
`Solution` are supporting special-case algebra, not the general hull or its
complexity. Keep these historical files unchanged; the new target repairs
both independent gaps without requiring the united set to be convex.
Useful semantic regression cases include `n=1`, `T={0}`, `b={1}` (empty),
`T={0}`, `b={0}` (all real solutions), `T=[0,1]`, `b={1}` (hull `[1,+∞)`),
and `T={1}`, `b=[-1,1]` (bounded hull `[-1,1]`). These are checks, not scope
restrictions or substitutes for the universal proposition.

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

The input is an $`n\times n`$ tridiagonal interval matrix $`\mathcal T`$, $`n\ge1`$, and an interval vector $`\mathcal b\subset\mathbb R^n`$, all with rational endpoints. Thus $`T_{ij}=0`$ for $`|i-j|>1`$, and the remaining entries of $`T`$ and all entries of $`b`$ range independently through their supplied closed intervals. Define the united solution set

```math
\Sigma(\mathcal T,\mathcal b)=\{x\in\mathbb R^n:\exists T\in\mathcal T\ \exists b\in\mathcal b,\ Tx=b\}.
```

Does a deterministic algorithm compute its exact coordinatewise interval hull in time polynomial in the total binary input length? It must report an empty solution set when appropriate; otherwise it must return

```math
\left[\inf_{x\in\Sigma}x_i,\ \sup_{x\in\Sigma}x_i\right],\qquad i=1,\ldots,n,
```

with infinite endpoints explicitly represented. Finite endpoints are returned exactly as rationals. No regularity promise is imposed: intervals crossing zero and singular members are included. The input/output convention makes the source's request for a polynomial exact-hull algorithm precise; the target is the smallest box, rather than an arbitrary enclosure.

This is distinct from computing the determinant range of the same interval family. It asks for rigorous optimal error bars on the solution vector of a structured uncertain linear system.
<!-- canonical-target-end -->
