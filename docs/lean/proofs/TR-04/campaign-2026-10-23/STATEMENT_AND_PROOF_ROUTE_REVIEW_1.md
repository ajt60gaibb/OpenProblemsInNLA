# TR-04 next-campaign statement and proof-route review

23 October 2026. Reviewer: `/root/recover_geometry`. This is the first renewed
proof-route review, prepared while TR-06's independent final audits run. It
contains no new Lean proof, solver implementation, kernel execution, CI,
Comparator, or canonical-status claim. The original problem and every
existing source remain unchanged. A second independent review should bind
this review and its inputs before the new proof campaign starts.

TR-04 is the recommended next target. Its complete mathematical route is
finite-dimensional real linear algebra with a finite search through tied
singular subspaces. The concrete shared target already has reviewed genuine
rank, exact SVD, uniform program, input/output, and operation-count meanings.
This avoids starting with an unformalized harmonic-analysis estimate,
probabilistic chaining theorem, general algebraic-degree calculation, or
polynomial-bit-time LP implementation. It is still substantial work: the
existing two counting lemmas do not prove either the approximation guarantee
or a uniform machine implementation.

## Current inventory and reuse boundary

At the recorded inventory snapshot, the canonical registry has 217 IDs: 83 Lean verified, 35 Solved,
62 Partially resolved, 36 Open, and one Solution claimed. The accompanying
`NEXT_TARGET_INVENTORY.json` records every current Solved entry, its original
canonical path and source presence. Source presence is not proof approval.
At that snapshot TR-06 remains Solved while its complete new proof is undergoing independent
and canonical verification, so it is excluded from this next selection.
FR-05, MD-03/04, RA-10, SP-11/12, TR-14 and PF-05 already have the completed
campaign work reflected in their current verified status and are excluded.
The earlier October campaign inventory is retained as historical evidence.

TR-04 has no shared `NLA/Proofs/TR04` program in this checkout. Its canonical
`lean/Solution.lean` proves only
`candidate_count_le_first_mode` and `cyclic_window_count_le_first_mode`.
These statements can be retained and reused. No active TR-04 proof assignment
was present in the supplied campaign inventory or current agent task tree;
this is not a claim about unrelated app chats or unpublished external work.
The previous statement and two independent boundary approvals remain useful.

The old canonical `lean/Challenge.lean` is not an adequate final boundary:
it takes `unfoldingRank` as an arbitrary input field and quantifies a free
function separately for each format, with a returned natural bounded by the
first mode size. That natural does not count machine steps. Proving that old
interface would not prove the current reviewed computational target. Preserve
its bytes and history; do not silently reuse it as the complete new target.

For comparison, SP-14 has 90 substantial partial supports but its actual
background inverse, infinite symbol, two-sided nonextension, and final
spectral-distribution gap remain large analytic gates. IE-26 and SP-13 need
weak-type harmonic-analysis inputs absent from their formal proof programs.
The interval LP and NP-hardness entries also require their full concrete
complexity semantics. In particular, IV-02/IV-04's frozen `Target` is an
unconditional polynomial-solver proposition, while the recorded resolution
is an equivalence with P=NP; an iff classification is not a proof of that
unconditional positive proposition. Their eventual proof boundary needs to
state the resolution while retaining the original question, rather than
assuming a complexity separation or proving a different assertion.

## Exact original problem

Permanent ID: TR-04. Canonical path:
`tensor-computations/TR-04/README.md`.
Resolution source: the complete Colbrook manuscript
`references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-04.tex`,
Theorem 3 with Sections 2–4. Its raw-byte SHA-256 is
`e7770aa08ee91fbda82e0bfe3e087f1a9c8ee2a076218144bf0040e4d282bf73`.
The existing complete-source informal review was also read.

For every order d at least three, all mode sizes at least two, arbitrary
positive prescribed cut ranks, and every dense real input tensor A, produce
one feasible tensor X by a single uniform polynomial-cost exact
arithmetic/SVD program. Feasibility means the actual real matrix rank of
*each* prefix/suffix unfolding is at most its prescribed bound. If the
optimal squared Frobenius error E is positive, require error(X) strictly less
than (d−1)E. If E is zero, require X=A exactly. Do not increase ranks.

This is a strict pointwise guarantee. It does not require a uniform smaller
constant, a fixed positive gap, floating-point robustness, or polynomial
binary bit complexity. The source's fixed-format family approaches d−1;
a proof must not strengthen the target to a uniform factor below d−1.

## Literal Lean boundary

Use the existing, unchanged
`NLA.Statements.TR04.Target`, with frozen counterpart
`NLA.ReviewedStatements.TR04.Target`. The intended eventual theorem is exactly
`NLA.Proofs.TR04.target : NLA.Statements.TR04.Target`, not an approximation
lemma with an external solver or runtime premise. In the namespaces opened
by the source, the complete definition is:

```lean
def Target : Prop :=
  ∃ P : Program, ∃ C k : ℕ, 1 ≤ C ∧
    ∀ S : Shape, ∀ r : Ranks S, (∀ j, 1 ≤ r j) → ∀ A : Tensor S,
      (∃ trace : Trace P, LegalTrace P (Start P S r A) trace) ∧
      ∀ trace : Trace P, LegalTrace P (Start P S r A) trace →
        ∃ t : ℕ, ∃ X : Tensor S,
          Returns P S (trace.state t) X ∧
          CostThrough P trace t ≤ C * Size S r ^ k ∧
          Feasible S r X ∧
          (0 < Optimum S r A →
            FrobeniusSq S A X < ((S.order : ℝ) - 1) * Optimum S r A) ∧
          (Optimum S r A = 0 → X = A)
```

`Shape` includes precisely the order/mode lower bounds. `Unfold` uses the
complementary finite mode-index sets and their actual joined tensor entry;
`Feasible` uses `Matrix.rank` over the reals. `Optimum` is the real infimum of
all feasible squared errors. `Returns` requires a genuinely halted address
and all original-shaped tensor coordinates in the indexed store.
`Size = DenseSize + order + sum ranks + 1`. All ranks are numerical parameters,
so a polynomial in this size does not assert a polynomial in their binary
encoding length.

The exact machine has finite instruction syntax and a fixed finite constant
pool. Scalar memory, arithmetic, comparisons, and natural-counter operations
are charged. Its full rectangular SVD response must have orthogonal square
U,V, nonnegative descending singular values, and exact reconstruction. The
three output blocks must be disjoint, the whole old input is read before
writes, and each SVD costs `(rows + columns + 1)^3`. Division by zero and
negative square-root inputs fail. There is no real-to-natural conversion,
rank oracle, optimization oracle, or uncharged matrix multiplication.
The target both requires a legal trace and quantifies over *every* legal
trace, including every valid tied/zero singular-space basis response.

The 28 September independent boundary approvals match the present intended
model. Their previous compiler/control results are historical statement
checks, not a solver proof. `input-lock.json` binds the currently inspected
sources for this renewed review.

## Mathematical proof route

First prove the finite matrix/SVD facts with complete rectangular and zero
cases. Construct a valid full SVD for every real matrix from the finite
self-adjoint spectral theorem, extend the positive image vectors to complete
orthonormal bases, and retain descending nonnegative values. For *any* tuple
satisfying `ValidSVD`, prove the rank/tail-energy and best rank-approximation
facts needed below; correctness must not depend on the tuple chosen in the
existence construction.

Prove feasibility is nonempty and closed, and prove `Optimum` is nonnegative
and attained. Zero is feasible. The rank constraints are closed determinantal
conditions, reshaping is continuous, and a minimizing sequence can be confined
to a bounded finite-dimensional ball. This gives a best feasible comparison Y
for the proof and E=0 implies A itself is feasible. Y and E are never queried
by the algorithm.

Implement ordinary TT-SVD mathematically with actual mode contractions,
reshape bijections, ranks and squared-sum norms. Prove its universal comparator
bound from the successive orthogonal truncation residuals. The published
[Oseledets paper, Theorem 2.2 and Corollary 2.4, pp. 2299–2300](https://users.math.msu.edu/users/iwenmark/Teaching/CMSE890/TENSOR_oseledets2011.pdf)
was re-read: it supplies the residual-sum argument and existence of a best
bounded-rank approximation. These are proof obligations to formalize, not
an imported Lean theorem or an allowed new axiom.

For an orthonormal first-mode factor U with projector P and at most r₁
columns, compress A by U transpose and merge its first two indices. Complete
at the unchanged remaining ranks and lift back to X_U. For every feasible Y,
prove the exact source completion bound

```math
\|A-X_U\|_F^2
\le \|(I-P)A\|_F^2+(d-2)\|P(A-Y)\|_F^2.
```

The first discarded component and the lifted completion residual are
orthogonal. Compression and lifting preserve every relevant rank cap through
actual left-multiplication identities on each unfolding. This proof must
retain the projected comparator residual; substituting only the full E at
this stage loses the strict tie argument. When d=3 the completion is one
matrix truncation. Do not recursively invoke the reviewed `Shape` type at
order two: the auxiliary TT-SVD theorem needs a separate order-two base case.

For the first unfolding, let e be the discarded squared singular-value tail
at r₁. Then e≤E. If its rank is at most r₁, use its column-space projector.
Otherwise the boundary singular value τ is positive. Let H contain the
strictly larger singular directions and Eτ the complete τ singular space.
Set h=dim H, t=dim Eτ and s=r₁−h, so 1≤s≤t. If s=t, test H plus all Eτ. If
s<t, from whatever orthonormal τ-basis the legal SVD supplied, test the t
cyclic windows of s basis vectors and add H. Every tested projector discards
exactly e, and every τ-basis vector appears in exactly s windows.

The best rank-approximation equality case needs an explicit proof. If a
feasible Y attains e=E>0, write S for the first-unfolding column space of Y.
Orthogonal decomposition forces Y=P_S A and S to maximize captured singular
energy. In a left eigenbasis, an orthogonal projector's diagonal weights lie
between zero and one and sum to dim S≤r₁. Since τ>0, maximal energy forces
rank r₁, weight one above τ² and zero below. Hence H is contained in S and
P_H(A−Y)=0. When s=t the whole Eτ space is also contained in S. Do not assume
uniqueness of Y, a spectral gap, full matrix rank, or a τ-basis aligned with Y.

If e<E, every tested completion has error at most e+(d−2)E<(d−1)E. In the
remaining e=E>0 case, the single s=t projector annihilates the optimal
residual and has error at most E. For s<t, the cyclic average gives

```math
\frac1t\sum_j\|P_j(A-Y)\|_F^2
=\frac{s}{t}\|P_{E_\tau}(A-Y)\|_F^2
\le\frac{s}{t}E<E.
```

At least one completion therefore has error at most
`(1+(d−2)s/t)E<(d−1)E`. The program compares the actual errors of all its
candidates, so the least-error one inherits this bound without knowing Y,
E, or the favorable window. Exact zero optimum follows from the completion
bound with Y=A. Handle A=0 separately before choosing an empty column space.

Finally construct a *concrete fixed program* for these loops and prove its
simulation, termination and cost for all legal SVD traces. One candidate
count bound is insufficient. Charged loops must recover integer mode/rank
counters from their exact real input values by counter/cast/comparison, build
all layouts, allocate disjoint output blocks, form every contraction and
matrix product, evaluate errors, choose a fixed-index minimum, and materialize
all N output coordinates before returning their address. Counters and memory
support arbitrary order; no format-dependent control graph or advice may be
chosen after the input.

Use conservative fixed polynomial bounds rather than optimized cost constants.
The number of candidates is at most n₁, there are d−2 completion cuts per
candidate, and all array dimensions can be capped by the actual dimensions
and numerical input ranks. Prove uniform bounds in `Size`, charge all full
SVD outputs, and include scalar reshaping/copying/error work. This yields
some fixed natural C,k, chosen before every input and every response trace.
The source's informal polynomial-cost paragraph motivates this construction
but does not by itself implement the finite instruction witness.

## Hidden assumptions to reject

| Issue | Required handling |
| --- | --- |
| Tied or zero singular values | Every valid response is permitted; the cyclic argument works for every τ-basis and every completion basis. |
| Oversized/inconsistent positive ranks | Cap actual work by dimensions; preserve the original prescribed inequalities without adding rank-consistency promises. |
| Empty dimensions/zero internal blocks | Prove full SVD totality for empty rectangular cases; show the program's actual allocations and branches are valid. |
| Best approximation | Prove closedness, bounded minimizing sequences, attainment and E=0 feasibility; no optimizer in machine input. |
| Strictness | Treat e<E, e=E with s=t, e=E with s<t, and E=0 separately. Do not replace `<` by `≤` or claim a uniform smaller factor. |
| Tensor/array semantics | Prove each mixed-radix/reshape bijection and rank identity; a tensor factorization diagram is not a stored-array simulation. |
| Legal traces | Prove existence and all-trace correctness; no favorable SVD selector or nonexistence loophole. |
| Exact arithmetic | Use legal comparisons and guard division/square root; no tolerance-based tie test or real-to-natural opcode. |
| Runtime | Exhibit one actual finite Program and fixed C,k; no returned cost field or uncharged TT-SVD oracle. |
| Output | A real halted pointer must address every computed output entry, not an existential free tensor. |

## Pinned-library feasibility and staged reviews

The pinned Mathlib source has
`LinearMap.IsSymmetric.eigenvectorBasis`, `eigenvalues_antitone`, and the exact
`LinearMap.singularValues` sequence with nonnegativity, antitonicity,
zero-padding and support/rank facts. These were inspected in the local pinned
`Spectrum.lean` and `SingularValues.lean`. The targeted source search did not
locate a ready-made full rectangular `SVDMachine.ValidSVD` theorem or the
needed best-approximation equality classification. Those remain explicit
formal work, not an assertion that no related API exists anywhere.

The matrix totality theorem also supports RE-05/RE-06: their
`NonadaptiveMatrixQuery.ValidSVDResult` is defined using exactly this same
`SVDMachine.ValidSVD`. Their `exactSVD` has a fallback until SVD totality is
proved. This reuse is an additional reason to prioritize TR-04 foundations.

Recommended reviewed milestones are: exact full SVD totality and its
basis-independent consequences; closed rank/optimizer and reshape lemmas;
TT-SVD universal completion bound; projector equality characterization;
finite cyclic average and strict mathematical algorithm; concrete program
simulation/cost; then a literal full-Target theorem and fresh original/frozen
identity, kernel/axiom, independent source, CI and Comparator evidence.
No conditional milestone may be described as the full target. No original
ID, path, mathematical target, archived proof or canonical status changes
are authorized by this review.
