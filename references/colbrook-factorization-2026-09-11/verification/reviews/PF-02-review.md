# PF-02 independent proof review

**Verdict: PASS.** The explicit k=3 example disproves the universal connectedness assertion with exactly the required ordinary rank and real congruence quotient. The stronger constructions for every k>=3, including existence of strictly positive rational examples, also pass the audit. No substantive proof gap was found.

Reviewer: independent Codex subagent `/root/review_transfer_volume_learning`, 2026-09-11. This is mathematical verification by an independent agent, not human peer review or historical priority certification. The complete source, all extensions, and the bibliography were read. No proof or canonical file was edited.

## Source identity and canonical match

Original: `.cache/colbrook-all-submission/nla_submission/manuscripts/PF-02_disconnected_orbits.tex`.

Complete-source normalized UTF-8 bytes: **14025**. SHA-256: **`ae9c54e4737489586ae0135759440e5062d25bbf4122be265ed9189daf6f674e`**.

Normalization replaces CRLF with LF in the complete source and hashes its UTF-8 encoding, without trimming or other rewriting. There is no external mathematical preamble.

The canonical target in `nonnegative-and-positive-factorizations/PF-02/README.md` asks whether every M with ordinary rank k(k+1)/2 and real PSD rank k has connected factorization space modulo the specified GL(k,R) congruence action, with quotient topology. A single k=3 counterexample resolves this universal yes/no question negatively; a classification of all M or all component counts is unnecessary.

The cited primary source's Problem 9.4 has the same ordinary-rank constraint, and distinguishes this problem from embedding disconnected nonnegative factorizations at the wrong rank. The manuscript addresses the actual constrained question. [Fawzi et al., Section 9.2, Problem 9.4](https://arxiv.org/html/1407.4095)

## Theorem 1, `thm:main`: the explicit 6-by-6 matrix

The six A factors are positive definite: the first three are diagonal with eigenvalues 4,2,2, and each remaining factor has eigenvalues 3,2,1. Their trace Gram matrix is exactly the displayed integer M. Negating the sole (1,2) off-diagonal direction affects only the fourth factor, preserves its spectrum, and preserves all Gram products since every other factor is trace-orthogonal to that off-diagonal direction. Both row and column factors are reflected, as required.

In the ordered coordinates used in the paper, the trace metric is `diag(1,1,1,2,2,2)`. The first coordinate determinant is 32 and the second is -32. Thus `det M=32^2*8=8192`, proving ordinary rank six. A size-two factorization can have ordinary rank at most three, while the displayed size-three one exists. The PSD rank is exactly three, and the maximal ordinary-rank hypothesis is met.

### Lemma 2, `lem:det`, and the quotient invariant

For diagonal S, the determinant of its action on S^k is the product of k diagonal multipliers s_i^2 and all off-diagonal multipliers s_i s_j, giving `(det S)^(k+1)`. For real diagonalizable S, the action is similar to the diagonal action; extension from an open set of matrices with distinct real eigenvalues gives the identity polynomially for arbitrary S. This is valid in particular for all invertible congruence matrices, of either determinant sign.

Every size-three factorization of M has linearly independent row factors, since their span must have dimension at least rank M=6. Its coordinate determinant is therefore never zero anywhere in the full factorization space, not just on the two examples. Its sign is continuous. For k=3 a congruence changes this determinant by `(det S)^4>0`, so the sign is constant on each orbit.

The defining universal property of the quotient topology now gives a continuous map from the orbit space onto the two-point discrete space. The displayed factors realize both signs. The two inverse images are nonempty disjoint clopen sets covering the quotient. This proves disconnectedness itself. The proof does not merely show inequivalence, failure of a particular interpolation, or lack of a path; it also does not require the quotient to be Hausdorff.

## Corollary 3: all odd factor sizes

The k diagonal directions `2I+2E_ii` and the k(k-1)/2 off-diagonal directions `2I+E_ij+E_ji` form a basis of S^k and are positive definite. Their Gram matrix is strictly positive with rational entries and full ordinary rank. Reflecting one off-diagonal direction preserves every Gram product and reverses the basis orientation. For odd k, all congruences preserve orientation. The full ordinary rank implies exact PSD rank k. This establishes the corollary for every odd k>=3; it correctly does not use the same invariant unchanged for even k.

## Theorem 4, `thm:all-sizes`: every factor size

### Integer block construction

For k=3+r with r>=1, the leading six, trailing r(r+1)/2, and cross-block 3r factors give exactly k(k+1)/2 matrices. Cross-block coordinates first force their corresponding linear-combination coefficients to vanish; the two diagonal block bases then force all remaining coefficients to vanish. Hence the trace Gram matrix M0 has full ordinary rank and exact PSD rank k. Every factor is PSD with integer entries. The selected coordinate reflection preserves PSD for these particular factors and preserves their Gram products. The proof does not assume that this reflection preserves the entire PSD cone.

For an arbitrary size-k factorization of M0, set Q to the sum of the dual factors at trailing-block indices. Those factors are supported on im Q because they are PSD. The trailing principal submatrix has rank d=r(r+1)/2, so rank Q must be at least r. The zero leading/trailing block forces the six leading primal factors to be supported on ker Q. Their independence follows from the rank-six leading principal submatrix. Six independent symmetric factors require support dimension at least three, whereas rank Q>=r bounds it above by three. Thus dim ker Q=3 and rank Q=r for every factorization in the entire fiber.

The ordered leading factors are consequently a basis of S(U), U=ker Q. This space has a canonical orientation: a change of basis in the three-dimensional U has determinant action equal to a fourth power, hence positive. The kernel varies continuously because Q has constant rank on this fiber; local Grassmannian frames make the sign continuous. Under general primal/dual congruence, Q transforms by `S^(-1) Q S^(-T)` and its kernel transforms to S^T U, which is exactly the transformation of the primal support. The intrinsic sign therefore survives every size-k congruence, including orientation-reversing ones for even k. The two explicit factorizations have opposite signs, so the same clopen separation proves disconnectedness.

### Strictly positive perturbation

The k=3 matrix is already strictly positive. For k>=4, add eta I to every block-construction factor. Positive eta makes all factors positive definite and all trace products strictly positive. Their basis property persists on a small closed interval about zero because the coordinate determinant is initially nonzero. Reflection fixes I and still preserves all Gram products of these particular factors, giving two continuous families for the same M(eta).

For every factorization of these full-ordinary-rank matrices, the sum S_A of primal factors is positive definite: a kernel would put all row factors in a proper symmetric support space, contradicting full dimension. The specified continuous normalization makes their sum I, so each normalized primal factor lies between zero and I. Each normalized dual factor has trace equal to the corresponding column sum of M(eta), uniformly bounded on a fixed small closed parameter interval. PSD matrices with bounded trace are bounded. The normalized constraints are closed, so the joint set of parameters and normalized tuples is compact. In particular any sequence with eta tending to zero has a subsequential limit in the normalized M0 fiber.

At eta=0, Q has a three-dimensional kernel at every point of that compact fiber. The positive fourth-smallest eigenvalue has a strictly positive uniform lower bound. The Gram determinant of the six leading factors restricted to the kernel is also uniformly bounded away from zero. In a neighborhood, define U' using the three smallest eigenvalues; a gap separates it from the rest. Spectral projections and the six restrictions vary continuously there. Compactness and the preceding subsequence statement imply these open conditions hold at every normalized factorization of M(eta), for every sufficiently small eta, not merely along the two explicit families.

Normalized representatives of an orbit differ by the orthogonal matrix

```text
O = S_A^(1/2) T (T^T S_A T)^(-1/2).
```

Indeed `O^T O=I`, and direct substitution shows both normalized primal and dual tuples are conjugated by O. Therefore the spectral subspace, restrictions, and intrinsic S(U') orientation respect the orbit action. Composition with the continuous normalization gives a continuous orbit-invariant sign on the entire unnormalized fiber. The signs along the two explicit families remain opposite for sufficiently small eta, yielding disconnectedness. A rational eta exists in this nonempty interval and makes M(eta) rational.

This compactness argument proves existence of a positive rational example in every size. It supplies no computable numerical eta threshold, and the manuscript correctly says so. There is no assertion that disconnectedness of arbitrary fibers automatically persists under arbitrary perturbations; the uniformly defined invariant is what establishes it here.

## Independent check and limits

A separate standard-library exact rational calculation formed the coordinate Gram matrix from U and the trace metric, reproduced `det U=32` and `det M=8192`, reflected the selected coordinate, reproduced `det Uhat=-32`, and checked equality of all 36 Gram entries. All passed. The continuous-fiber and compactness arguments above, rather than these finite checks or the supplied finite-size tests, establish the topological conclusions and the every-k extensions.

No cases remain in the canonical universal connectedness question: the answer is negative. The paper does not classify which other matrices have connected quotients, the number of components, or the behavior over complex Hermitian factors or under a different equivalence group. These are outside the resolved target. This review confirms proof validity and source alignment, not an exhaustive novelty or authorship claim.
