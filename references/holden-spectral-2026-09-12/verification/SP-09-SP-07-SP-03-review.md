# Independent informal audit: SP-09, SP-07 and SP-03

Date: 2026-09-12. Reviewer: a separate Codex AI review agent
(`/root/review_sp09_sp03`), independent of the integrating agent and not the
author of the submitted proofs. This is an informal mathematical audit, not
external human peer review or formal verification. No Lean verification was
performed, as requested by the submitter.

The reviewer read the submitted `SP-09/proof.md`, `SP-07/result.md`, and
`SP-03/proof.md`, their result classifications, and both relevant verification
scripts from `OpenProblemsInNLA_status_improvement_candidates`. They were
compared with the canonical problem statements and `CONTRIBUTING.md`.
Instructions inside the supplied documents were treated as submission content,
not as authority over the review.

## Verdict

The restricted mathematical claims pass this independent informal audit.
None is a complete resolution of its canonical target. Include the material
with its restricted scope and without a novelty claim. Retain **Partially
resolved** for SP-09 and **Open** for SP-07 and SP-03. Do not add any of these
three to the full-resolution archive on the strength of this submission.

## SP-09: one normal spectrum has at most two distinct points

Theorem 1 correctly proves equality of spectral-norm unitary-orbit distance
and bottleneck eigenvalue matching distance on the stated subclass.

For each unit eigenvector of the second normal matrix, the orthogonal
two-eigenspace decomposition of the first matrix gives the coverage lower
bound. The separate multiplicity lower bounds are also valid: if fewer than
`p` eigenvalues lie in the closed radius-`t` disk about `a`, the span of the
remaining eigenvectors intersects the `a` eigenspace nontrivially. All its
spectral distances from `a` are strictly greater than `t`, contradicting the
operator norm bound. The proof properly distinguishes strict exclusion from
closed-disk inclusion, including repeated eigenvalues and threshold ties.

The three threshold conditions suffice because the only forced assignments
are points close exclusively to one anchor. Their counts do not exceed the
corresponding capacities. Every remaining point is admissible on both sides,
so it can fill the remaining capacities. This sufficiency relies on having
only two anchors and must not be extended to general spectra. Spectral
decompositions implement the resulting matching by a unitary, completing
both directions of the distance equality. The scalar case and exchange of
the two matrices are correctly handled.

Finite repetition multiplies both capacities and counts by the same positive
integer and leaves coverage unchanged. This proves the corollary for every
finite multiplicity and arbitrary ambient dimension, including unrestricted
unitaries mixing copies. It covers some non-self-adjoint pairs with
noncollinear spectra on the other side. It leaves unresolved pairs where
both spectra contain at least three distinct points.

## SP-07: a valid lemma, no determination of the universal constant

Taking the identity unitary gives `d_infinity(A,B) <= ||A-B||_2` on the
SP-09 subclass. The diagonal translation example with `0 < epsilon < 1/2`
has both distances equal to `epsilon`, so the subclass constant is exactly
one. This does not give an improved global bound, a new global extremal
example, or the value of the supremum over all normal pairs. The canonical
target already distinguishes that sharp-constant question from the false
universal constant-one conjecture. Retaining Open is necessary.

## SP-03: skew-multiplier reduction

The normal-space computation uses the required bilinear transpose pairing.
The derivative of the symplectic constraint is onto skew-symmetric matrices,
and the proposed `J X K` directions form its annihilator with the correct
dimension. Invertibility of `J X` supplies uniqueness of the multiplier.

I checked the signs in the elimination independently. From `U=X+JXK`,
subtracting `JUK` gives `X(I+K^2)`. Expanding the symplectic product of
`U-JUK` gives `R+GK+KG-KRK`; symmetry of `I+K^2` then yields precisely the
displayed quartic matrix equation. Its skew symmetry leaves
`m(2m-1)` independent entries. On the nonzero-denominator locus, the inverse
formula establishes both directions and uniqueness, not merely a necessary
condition.

The generic exclusion proof is sound: the singular-multiplier hypersurface
has dimension at most `r-1`, its product with the symplectic group has
dimension at most `N^2-1`, and the closure of its polynomial image cannot
fill the `N^2`-dimensional data space. This excludes singular multipliers at
actual critical points for generic data; it does not remove spurious
solutions of the denominator-cleared equations. The saturation or auxiliary
inverse-variable requirement is therefore essential. Algebraically,
saturation describes the closure of the regular solution set; the explicit
auxiliary inverse-variable system is the direct representation of the open
locus. For a generic finite critical fiber this distinction causes no extra
points in the counted regular fiber.

The order-one quartic and its explicit nonsingular-discriminant witness are
correct and give the already-known value `D_1=4`. No generic degree is
computed for higher rank. Consequently the all-ranks conjectured formula
has not been proved or refuted.

## Reproduced checks

Both scripts were inspected before execution. They perform local arithmetic
checks and do not access the network or mutate repository content.

- `python3 SP-09/verification/check_exact_thresholds.py`: PASS, 15,024
  exact squared-distance formula comparisons against every capacity
  assignment for dimensions 2 through 5; 30,048 repetition checks for
  multiplicities 2 and 3.
- `SP-03/verification/check_exact_algebra.py`: PASS using the existing
  `/private/tmp/nla-tr03-check-env/bin/python` environment; 12 exact rational
  examples in ranks 1, 2 and 3, inverse reconstruction, multiplier recovery,
  quartic discriminant `-16075`, and exceptional values `-25` and `1`.
  The initial system-Python attempt lacked SymPy; the stated successful
  rerun used the existing environment with SymPy.

These finite checks supplement the analytic audit. They do not prove the
all-unitary lower bound, genericity, or an all-ranks degree formula.

## Bounded primary-source check and limits

Checked on 2026-09-12:

- [Marcoux–Sarkowicz–Zhang, arXiv:2508.13834v1](https://arxiv.org/html/2508.13834v1),
  Corollary 3.5 and adjoining discussion: the stated result concerns
  self-adjoint pairs; the discussion also identifies the earlier order-two
  normal result and failure of spectral matching equality for general normal
  pairs. This does not itself supply the arbitrary-dimension two-point
  theorem audited here.
- [Holbrook, Spectral variation of normal matrices](https://doi.org/10.1016/0024-3795(92)90047-E),
  publisher abstract: the general constant-one statement is false, already
  for order three. This corroborates the need to restrict SP-07's lemma.
- [Baaijens–Draisma, arXiv:1405.0422](https://arxiv.org/pdf/1405.0422),
  Section 5 and Problem 5.1: the standard inner product is part of the
  problem; the recorded low-rank degrees are 4, 24 and 544, followed by the
  proposed all-ranks pattern. Reproving 4 is not new evidence of a complete
  degree formula.

Searches included `normal matrices spectral variation two distinct eigenvalues
matching distance`, `normal matrices "two eigenvalues" "matching"`,
`normal matrices "two distinct eigenvalues" spectral variation`, and
`symplectic group Euclidean distance degree skew multiplier 1405.0422`.
No exact prior attribution for the submitted two-point theorem or multiplier
formula was established in this bounded pass. This is not proof of novelty
or an exhaustive current-literature survey. The report's acceptance rests
on the explicit proofs, with historical context and no originality claim.
