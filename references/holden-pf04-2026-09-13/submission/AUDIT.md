# Mathematical audit of the PF-04 proposed proof

## Scope and status

The manuscript presents a complete proposed argument for the universal real statement p₆ = 9. The argument has been internally checked against its stated hypotheses and accompanied by finite exact tests. It has not been independently reviewed or checked by a proof assistant. No mathematical gap is intentionally left as an assumption or conjecture beyond the explicitly cited published theorems.

The purpose of this file is to make the review targets explicit, not to certify the correctness of a research proof by assertion.

## External theorem dependencies

| Input | Precisely what is used | What is not being inferred |
|---|---|---|
| K1 | Every order-five CP matrix has cp-rank at most six. | No order-six bound follows from this alone. |
| K2 | The stated upper bounds for connected triangle-free graphs. | Singular trees are not assigned cp-rank equal to their order. Even-cycle cp-rank is not equated with ordinary rank. |
| K3 | Orthogonality to an exceptional extremal copositive matrix of order six implies cp-rank at most nine. | An arbitrary matrix with a zero entry is not assumed to satisfy this bound. |
| K4 | In K3, a zero diagonal entry of the normal gives the bound seven. | A singular positive semidefinite normal is not assumed exceptional. |

K3 and K4 are taken from the corrected arXiv v3 of Shaked-Monderer’s paper, dated 1 June 2017. The classification-dependent proof of that published theorem is not reproved here.

## 1. Topology and singular limits

**Obligation:** A bound on positive-definite matrices must extend to singular matrices without assuming continuity of cp-rank.

**Argument:** For a fixed column count r, pad factors with zero columns. If A_k = B_k B_kᵀ converges, then ||B_k||²_F = tr(A_k) is bounded. A convergent subsequence of the nonnegative factors gives an r-column factor of the limit. Since A + εI is CP, positive definite, and has the same off-diagonal support, this proves the required extension for r = 8 and r = 9 separately.

**Important distinction:** A factorization limit is justified by compactness of factors, not by an unsupported assertion that cp-rank is continuous.

## 2. Relative faces and completion

**Obligation:** A positive-definite boundary point with zero entries needs a normal that is not merely a nonnegative matrix supported on those zero entries.

**Argument:** Work in the linear space L_G with the nonedges fixed at zero. F_G is full-dimensional there because diagonal atoms and graph-edge atoms form a basis. A relative boundary point has a nonzero supporting functional P in L_G. Its clique blocks are copositive because every nonnegative rank-one clique atom lies in F_G.

The completion lemma is proved explicitly. Missing entries become geometric means of the diagonal entries. Zero-diagonal coordinates have only nonnegative specified incident entries and are removed. After diagonal normalization, moving mass between nonadjacent coordinates makes the quadratic form affine; moving to an endpoint reduces support without increasing its value. The final support is a clique.

**Why the normal is exceptional:** Complete P to a copositive Q and decompose Q into extreme rays. A positive-definite A cannot be orthogonal to a nonzero positive semidefinite summand. If all remaining summands were nonnegative, orthogonality and exact support would force every visible entry of P to be zero. This contradicts P ≠ 0.

**Review target:** Lemmas 3.1–3.2. No claim that all faces of the CP cone are exposed is used.

## 3. Shear direction and first exit

**Obligation:** The graph reduction must preserve complete positivity at its endpoint, preserve positive definiteness, not introduce forbidden support, and not pay an extra rank-one column.

**Argument:** For N_G[j] contained in N_G[i], use T(t) = I − t e_i e_jᵀ. The matrix T(t) is invertible for every real t, and its inverse is I + t e_i e_jᵀ, entrywise nonnegative for t ≥ 0. Hence A(t) = T(t) A T(t)ᵀ stays positive definite, and reconstructing A from A(t) cannot increase cp-rank. Neighborhood inclusion makes all original nonedges remain zero.

Relative interior gives a feasible initial interval. The entry a_ij − t a_jj becomes negative at finite t. The proof takes the first exit from the CP face, not an unjustified global convex feasible interval for this quadratic path. Closedness puts the endpoint in the face.

If its graph were unchanged, the relevant relative-boundary bound would contradict its high cp-rank. It therefore deletes an edge. This is what permits edge-minimal counterexamples to be excluded.

**Review target:** Lemma 3.4 and both minimal-edge arguments. The inverse, not T(t) itself, is the nonnegative matrix used in the cp-rank comparison.

## 4. Small supports and the prism

The degree-at-most-two bound is proved from a prescribed-row factorization in order three and K1. Group only the original columns positive at the chosen vertex, refactor their at-most-three-vertex block, and move columns zero at that vertex into the order-five remainder. For degree one, only one positive entry in the prescribed row is needed; for degree two, at most two are needed.

The prism argument groups all cross-triangle contributions on the three matching edges. Each 2-by-2 CP block is replaced by one edge vector plus nonnegative diagonal slack. Increasing one endpoint's allocation decreases one triangle's diagonal until that 3-by-3 block is singular and increases the other triangle's diagonal. Positive semidefiniteness and entrywise nonnegativity imply complete positivity in order three. The final count is 2 + 3 + 3 = 8.

**Review target:** Lemmas 2.3–2.4 and 4.2. No statement that arbitrary higher-order doubly nonnegative matrices are CP is used.

## 5. Terminal graphs

For a six-vertex graph of minimum degree at least three, the complement has maximum degree at most two. Closed-neighborhood inclusion in G is exactly reversed open-neighborhood inclusion in its complement. Isolated vertices, paths with at least three vertices, and 4-cycles in the complement are excluded explicitly. Its components can therefore only combine as 3K₂, 2C₃, or C₆.

This classification is proved analytically and also exhaustively checked. The labelled counts are 15 octahedra, 10 copies of K₃,₃, and 60 triangular prisms. Of the 4,095 proper subgraphs of one fixed octahedron, the only terminal ones are eight labelled prisms. K₃,₃ cannot embed because a size-three bipartition class cannot be a union of missing two-element pairs.

## 6. The positive-diagonal octahedral lemma

**Obligation:** Compress all possible zero columns, including nonminimal triangle zeros, without counting them as independent rays.

After normalizing the copositive diagonal to one, each factor column has support at most three. Edge zeros are e_i + e_j on edges with normal entry −1. Their graph H is triangle-free.

A full triangle zero makes the triangle block positive semidefinite. If it also contains an edge zero, the two independent kernel vectors force rank one; the zero is a nonnegative combination of exactly two edge zeros. Otherwise that triangle block has rank two and only one positive zero ray.

Let h be the number of H edges, c the number of octahedral triangles meeting H, and t the number of positive triangle rays on the other triangles. Then t ≤ 8 − c. Each H edge is in exactly two octahedral triangles, each containing at most two H edges, so h ≤ c.

The nonminimal zeros are not simply discarded. Their coefficient Gram matrix C is CP on h vertices. Two coefficient coordinates can co-occur only when their H edges form a triangle. Each H edge can have at most two such neighbors. Thus the coefficient graph has maximum degree at most two, K2 gives cpr(C) ≤ h, and multiplication by the nonnegative edge-zero matrix U preserves this bound. Therefore cpr(A) ≤ h + t ≤ 8.

**Review target:** Lemma 5.1. Normal zeros on missing matching pairs are irrelevant: factor supports are cliques of the fixed octahedron. The proof does not assume that every zero of the normal has support at most three—only the factor columns being used do.

## 7. No circularity in the proper-support bound

The bound eight on proper octahedral subgraphs is proved before the full octahedral bound nine. Its inputs are the eight-column relative-boundary result, the shear, small-support bounds, and the terminal classification. A full octahedron is excluded by strict edge containment; K₃,₃ cannot embed; the prism has the separately proved bound eight.

No nine-column factorization of an octahedral matrix is used to deduce the eight-column proper-support bound.

## 8. The singular full-octahedral endpoint

**Obligation:** A rank-one subtraction must not silently stop at an unhandled singular matrix or pay 9 + 1 columns.

For opposite triangles T and T′, the cross block of a positive-definite exact-octahedral matrix has zero diagonal and strictly positive off-diagonal entries. Its determinant is a*d*e + b*c*f > 0. This implies that every row of A⁻¹ has a nonzero restriction to T.

For v = e₁ + ℓe₃ + ℓ²e₅, each coordinate of A⁻¹v is a nonzero polynomial in ℓ of degree at most two. Six such polynomials exclude at most twelve integer candidates. Some ℓ in {1,...,13} therefore gives a full-support vector q = A⁻¹v.

At the maximum feasible subtraction R = A − t*vvᵀ, exactly one of the following applies:

| Endpoint | Bound for R |
|---|---|
| A support edge has vanished, with any rank | Eight by the proper-support proposition |
| Exact octahedral support and positive definite | Eight by the octahedral relative-boundary corollary |
| Exact octahedral support and singular | t* = 1/(vᵀA⁻¹v); Rq = 0; qqᵀ has positive diagonal; eight by the octahedral orthogonality lemma |

In the last line, qqᵀ is positive semidefinite, not exceptional. Lemma 5.1 was deliberately proved without extremality. The remainder's bound is eight in every case, so adding back the one peeled vector gives nine.

## 9. Exact lower bound

The displayed integer factor B* has nine columns, one for each K₃,₃ edge, with one coefficient changed from one to two. Its Gram matrix has determinant 36. Every nonnegative factor column must have clique support. Because K₃,₃ is triangle-free, one column covers at most one positive edge, and all nine edges require coverage. This proves exact cp-rank nine, not merely an upper bound or a numerical estimate.

## Verification limits

The verifier establishes its stated finite assertions with exact arithmetic. It does not prove the topological separation theorem, the compactness arguments, the classification of triangle zero cones, or the imported published theorems in a proof assistant. It does not search all real matrices. It does not establish independent novelty, publication acceptance, or community consensus.

The manuscript should therefore be evaluated as an explicit proposed proof, with particular attention to the identified lemmas, before a repository is marked resolved on its strength.
