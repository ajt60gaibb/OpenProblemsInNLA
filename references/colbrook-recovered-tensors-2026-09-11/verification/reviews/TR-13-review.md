# TR-13 — independent complete-source review

Reviewer: independent AI mathematical audit, 11 September 2026. The reviewer did not develop this recovered manuscript. This report is not external human peer review, formal verification, or a priority claim.

**Verdict: PASS for the full canonical TR-13 target.** For every fixed odd order m>=5 and every dimension n>=2, the proof establishes a nonempty Zariski-open set on which ordinary rank, symmetric rank, ordinary border rank, symmetric border rank, and Vandermonde rank all equal ceil((m(n-1)+1)/2). The stronger manuscript statement including m=3 is also justified. No material gap or required manuscript correction was found.

**Recommended status: Resolved, affirmative.** Preserve the canonical ID, path, generic quantifier, complex field, and unrestricted ordinary-border-rank convention. This is not a resolution of the separate all-Hankel-tensor problem TR-14.

## Complete source binding

Read the entire recovered TeX manuscript `.cache/tensor-recovered/tensor_recovered/manuscripts/TR-13/main.tex`, including abstract, all six sections and bibliography; the entire supplied `.cache/tensor-recovered/tensor_recovered/code/verify_tr13.py`; and the complete current `tensor-computations/TR-13/README.md` (reviewed status Open; last checked 2026-09-10).

Complete UTF-8 source hashes below replace CRLF with LF and perform no trimming or other normalization:

| Source | Normalized bytes | SHA-256 |
| --- | ---: | --- |
| `manuscripts/TR-13/main.tex` | 9769 | `14d65476284409e5db8d283120cb23bbb70566631ff7e76b6cded56b4d0c068c` |
| `code/verify_tr13.py` | 3180 | `c2e0b90e3fcdb67b6ae53038f0f44134e6f1a5bc8051af2565169711e9d79b68` |

These are hashes of complete original files, not rendered PDFs or extracted proof bodies. They were computed independently while reading the files and confirmed by the reviewer diagnostic.

## Theorem locators and exact target

- **Theorem 1**, `thm:main`, line 46: all five generic ranks and their common value.
- **Lemma 2**, `lem:koszul`, line 64, Section 2: arbitrary three-way border-rank lower bound and invertible-slice rank identity.
- **Section 3**, line 104, equations `eq:slices` and `eq:compression`: grouping and compression from the original tensor.
- **Section 4**, line 126, equations `eq:spikes`, `eq:shift`, `eq:comm`, and `eq:lower`: uniform witness, generic lower bound, and the n=2 branch.
- **Section 5**, line 181: dominant moment map and simultaneous equality on an open set.
- **Section 6**, line 217: precise generic-only scope and description of diagnostics.

The canonical uses one-based tensor entries indexed by h_(sum i_j-m); the source uses zero-based entries indexed by h_(sum i_j). These are identical after subtracting one from each tensor index. Both permit arbitrary complex rank-one summands for ordinary rank and unrestricted ambient approximating tensors for ordinary border rank. The manuscript explicitly preserves that stronger border-rank convention.

Opened the [Nie–Ye primary author preprint, arXiv:1706.03631v2](https://arxiv.org/pdf/1706.03631), including the rank definitions, Corollary 3.3, and Section 6. Question 6.1 and Conjecture 6.2 ask for the five-rank equality for generic odd orders at least five. Corollary 3.3 supplies the generic Vandermonde value; even-order and order-three results are distinguished from the remaining question. Conjecture 6.3 is the separate statement about ordinary and symmetric ranks for every Hankel tensor. The recovered proof addresses the exact generic question and does not invoke the stronger all-tensor conjecture.

## 1. Parameter arithmetic and all-order coverage

Write m=2k+1, ell=n-1, a=k*ell+1, s=floor(ell/2), and r=a+s. If ell=2s, then D=(2k+1)2s is even and ceil((D+1)/2)=k*ell+s+1. If ell=2s+1, then D is odd and (D+1)/2=k*ell+s+1. Thus r is exactly the proposed common value in both parity cases. There is no parity restriction on n.

For n>=3, ell>=2 and s>=1. The middle coordinates 0,s,2s are distinct and all at most ell. The lower-bound argument covers every integer k>=1, which includes the already-known cubic case and every canonical order m>=5. The n=2 case is handled separately and does not attempt to select three middle coordinates from a two-dimensional space.

## 2. Three-slice lemma and ordinary border rank

For a rank-one three-way tensor, each slice is c_j*u*v^T. Its block matrix is a Kronecker product up to row and column ordering. The scalar 3-by-3 matrix has the row relation

`c_2 row_1 - c_1 row_2 + c_0 row_3 = 0`.

If all c_j vanish the matrix is zero; otherwise this is a nontrivial relation. Therefore its rank is at most two. The Kronecker product has rank at most two as well, including zero vectors or zero slices. By linearity of K and subadditivity of ordinary matrix rank, every sum of q arbitrary rank-one tensors satisfies rank(K)<=2q.

Every (2q+1)-minor is a polynomial in the full three-way tensor entries. It vanishes on all tensors of ordinary rank at most q and hence on any entrywise limit of such tensors. Thus the bound applies to ordinary border rank in the entire tensor space; there is no requirement that the approximating tensors be symmetric, Hankel, or decomposed by Vandermonde vectors. This is the main distinction required by the canonical target, and it is satisfied.

For invertible M_0, direct block multiplication shows that a vector (x,y,z) lies in the kernel if and only if

`y=M_0^(-1)M_1 x`, `z=M_0^(-1)M_2 x`, and

`(M_1 M_0^(-1) M_2-M_2 M_0^(-1) M_1)x=0`.

There is a one-to-one correspondence between this kernel and the kernel of the displayed a-by-a matrix. Its nullity gives exactly the stated rank formula 2a plus the commutator-type rank. No simultaneous diagonalization, symmetry, or generic invertibility assumption is used in this identity; invertibility is verified for the witness where it is applied.

## 3. Compression is legitimate for arbitrary decompositions

Every integer u between zero and k*ell is the sum of k entries from {0,...,ell}, for example by filling the coordinates successively. Multi-indices chosen for distinct sums are necessarily distinct. Selecting one coordinate for each sum therefore is a fixed linear surjection from the grouped factor to C^a.

Grouping the first k factors, the middle factor, and the last k factors sends each original rank-one tensor to a three-way rank-one tensor. Applying the fixed selection maps and selecting the three middle coordinates sends it to another rank-one tensor or zero. The composition is linear and continuous on the full original tensor space. Applying it to each term of an arbitrary border-rank approximating sequence proves

`ordinary border rank(H) >= ordinary border rank(T(H))`.

The compressed entries are h_(u+v+js), since all selected multi-indices have the required sums. Their maximum index is 2a-2+2s<=2k*ell+ell=D. Thus every selected entry is defined. No inverse of the compression, preservation of all decompositions, or structured decomposition of H is assumed.

## 4. Two-spike algebra checked independently

The witness has nonzero generator entries at a-1 and 2a+s-1. The larger is at most D precisely when s+1<=ell, which holds for every ell>=2. They are distinct. Also a=k*ell+1>=ell+1>=2s+1. This last inequality ensures that the row and column ranges in the rank certificate are valid even in the smallest formats.

I independently recomputed the reversed-slice entries:

`(J M_j)_(u,v) = h_(a-1-u+v+js)`.

For the first spike, the equality of indices gives v-u=-js, which is exactly L^(js). For the second spike it gives v-u=a+s-js. When j=0 this exceeds the allowable maximum a-1; when j=1 it equals a, also impossible. When j=2 it equals a-s, giving the s entries E_(i,a-s+i)=1 for 0<=i<s. Therefore

`M_0=J`, `B=J M_1=L^s`, and `C=J M_2=L^(2s)+E`

hold entry by entry for all parameters, including s=1. In particular M_0 is invertible and M_0^(-1)=J.

The pure powers commute. Multiplying the elementary matrices gives

`E L^s = sum_(i=0)^(s-1) e_i e_(a-2s+i)^T`,

`L^s E = sum_(i=0)^(s-1) e_(s+i) e_(a-s+i)^T`.

Their difference has only the indicated 2s entries. In rows 0,...,2s-1 and columns a-2s,...,a-1 it is diag(I_s,-I_s). Its determinant is (-1)^s, and every other entry outside those row/column positions is zero. The commutator has rank exactly 2s, not merely at least 2s. The possible overlap between the selected row-index range and column-index range causes no problem: rows and columns are independently indexed in a matrix minor.

There is a harmless orientation change between the commutator displayed in Section 4 and the expression in Lemma 2. Substituting M_1=JB and M_2=JC gives

`M_1 J M_2-M_2 J M_1 = J(BC-CB)`.

The section computes CB-BC instead. Negation and multiplication by the invertible J preserve rank. Thus the application of the lemma is correct as written. It yields rank(K)=2a+2s=2r. The ambient size permits this rank because 2s<=a-1.

This witness certifies that at least one fixed 2r-by-2r minor of the matrix polynomial K(T(h)) is not identically zero in h. Its nonvanishing locus is a nonempty Zariski-open set. On that set rank(K)>=2r, so the border-rank bound and compression give ordinary border rank(H)>=r. The proof does not require the same witness to have generic Vandermonde rank or to belong to the eventual common open set.

## 5. Binary case

If n=2, then ell=1, s=0, a=k+1 and r=k+1. Grouping k factors against k+1 factors and selecting representatives for sums yields the a-by-(a+1) matrix with entries h_(u+v). At the witness h_k=1, its first a columns are the reversal matrix J. Their determinant is (-1)^(a(a-1)/2), which is nonzero. The same fixed minor is nonzero on an open subset of the binary Hankel parameter space.

An ordinary matrix flattening has rank at most the number of arbitrary rank-one original summands, and its minors survive entrywise limits. This therefore proves the required ordinary-border-rank lower bound for all binary odd orders too. The n=2 boundary has not been omitted or inferred from the unavailable three-slice selection.

## 6. Generic upper bound and simultaneous equality

For the moment map with r weighted nodes, at distinct finite nodes and all nonzero weights the Jacobian columns are the evaluation vectors and weighted derivative vectors. If a row covector annihilates every column, its coefficient polynomial f of degree at most D has both f(t_j)=0 and f'(t_j)=0 at r distinct points. Unless f=0, it would have at least 2r zeros counted with multiplicity. Since 2r>=D+1>D, that is impossible. Hence the Jacobian has full row rank D+1.

The nodes and weights meeting these conditions exist over the complex numbers. The polynomial map is thus dominant. Its constructible image contains a nonempty Zariski-open subset of C^(D+1). The constructibility step is important: dominance alone would only establish a dense closure, whereas here actual image points give actual decompositions. For each image point, the moment formula gives an exact sum of at most r Vandermonde powers in the original m-way format. Finite nodes already suffice on this open set; allowing the projective point at infinity in the rank definition does not weaken the conclusion.

The Hankel parameter map is linear and injective, because every sum between zero and D occurs as a tensor index sum. Its parameter space is irreducible. Consequently the two nonempty Zariski-open sets, one for the ordinary-border-rank lower bound and one inside the moment-map image, intersect nontrivially. On the intersection,

`r <= ordinary border rank <= ordinary rank <= symmetric rank <= Vandermonde rank <= r`.

Likewise ordinary border rank <= symmetric border rank <= symmetric rank. All five quantities are therefore equal to r on one common open set. This proves the exact quantifier in the canonical target for each m,n, rather than separate generic assertions whose exceptional sets were left unmatched.

## 7. Supplied code inspection and independent diagnostics

The entire supplied `verify_tr13.py` was read before any execution decision. It uses SymPy exact matrices and no floating-point tolerance. It checks 45 shift-certificate cases, 9 binary cases and 12 rank-one cases, computing the full Koszul rank for its stated smaller subset. It writes `evidence/TR-13.json` relative to its own location. Its formulas and expected ranks agree with the manuscript, including r=(m*ell+2)//2, the spike bounds, and the commutator minor. Its finite grid is diagnostic only and is not a proof of the uniform statement.

The reviewer did not rerun that supplied script in its source directory. The default available Python environment did not contain SymPy. Instead, a separate reviewer-authored standard-library program was created and executed, without importing any submission code or third-party package:

- `.cache/tensor-recovered/reviews/reviewer_tr13_exact.py`
- `.cache/tensor-recovered/reviews/reviewer_tr13_exact.json`

It directly constructs the full Koszul matrices and computes ranks by `fractions.Fraction` Gaussian elimination. All checks passed:

| (m,n) | Direct full Koszul rank | Required 2r |
| --- | ---: | ---: |
| (3,3) | 8 | 8 |
| (3,4) | 10 | 10 |
| (5,3) | 12 | 12 |
| (5,4) | 16 | 16 |
| (5,6) | 26 | 26 |
| (7,5) | 30 | 30 |
| (9,4) | 28 | 28 |

The independent program also verified the binary flattening ranks for m=3,5,7,9,11 and full row rank of the moment-map Jacobian at integer nodes with unit weights for D=5,6,10,15. The output records the complete source/code hashes above. These checks independently confirm representative algebra and both parity cases; the all-parameter proof is the symbolic argument reviewed in Sections 1–6 of this report.

## Final disposition

**PASS: the full generic TR-13 conjecture is established by the reviewed source.** The uniform nonzero-minor construction proves the strongest lower rank needed, ordinary border rank with arbitrary approximants. The dominant moment map supplies the matching generic actual Vandermonde rank upper bound. Both boundaries n=2 and m=3 are covered, and every canonical pair m odd>=5, n>=2 is included.

No conclusion is certified for equality at every exceptional Hankel tensor, real-rank versions, decomposition algorithms, or historical novelty. No original manuscript, supplied code, or canonical problem file was edited.
