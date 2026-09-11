# IV-06 independent counterexample review

Review date: 2026-09-11. The complete manuscript and complete `common.tex` were read, and all membership and exclusion calculations were checked independently. No manuscript or canonical file was edited.

## Verdict and exact target

**PASS. Recommend IV-06 be recorded as resolved by counterexample: the asserted bound of n connected components is false already for n=3.** The manuscript proves at least four components, which suffices; it does not claim to enumerate the entire real eigenvalue set or every endpoint. No novelty, author-identity, or priority determination is part of this verdict.

The exact canonical target is `intervals-and-absolute-value-equations/IV-06/README.md`. It concerns the union of real eigenvalues over a real interval matrix with independent entries and permits singleton intervals, with no symmetry requirement. The submitted family

\[
A(a,b)=\begin{pmatrix}25&a&b\\1&-1&0\\1&0&1\end{pmatrix},
\quad a\in[-166,-16],\quad b\in[9,159]
\]

is exactly such a three-dimensional interval family. Only two distinct entries vary, independently. The fixed entries do not violate the canonical quantifiers. This is a counterexample to the general real-eigenvalue union assertion, not to the symmetric-family result or to a claim about the complex spectrum of one fixed matrix.

## Source identities and coverage

Paths are relative to `.cache/colbrook-package-submission/nla_submission/`. Hashes cover the complete UTF-8 source after replacing CRLF by LF, without trimming.

| File | Normalized bytes | SHA-256 |
|---|---:|---|
| `manuscripts/IV-06.tex` | 3,524 | `b96d7f17560f925329a725ec98c52beec4f2b5fa089e8bcb89edc473c39ab4fe` |
| `manuscripts/common.tex` | 985 | `d8e7a0de2ed1a1fd162b147211fe29c7b1d7bfbc0be7b827dcda4d9a2653d0d4` |
| `code/verify_exact.py` | 10,215 | `f7ef316edcb336e64b07372613223c6d96e014a2c338508b86871d73138b549a` |
| `code/nla_algorithms.py` | 7,968 | `47cd54ef30094e0bfa6ffd89ff8678c28d57d35a16f17783b3be0f22488a82a0` |

Coverage includes the abstract and family definition, Theorem 1 (line 19), the full polynomial expansion and exact range formula `eq:range` (line 30), every witness and separator, the topological conclusion, and all scope statements (line 63 onward). `common.tex` supplies only standard definitions and presentation commands. The relevant verification function is `verify_iv06` in `verify_exact.py`; its helper imports do not replace the exact arithmetic in that function.

## Independent algebra and interval audit

Direct expansion before centering gives

\[
\det(\lambda I-A)=(\lambda-25)(\lambda^2-1)-a(\lambda-1)-b(\lambda+1).
\]

Substituting a=-91+d_1 and b=84+d_2 yields

\[
p(\lambda;d_1,d_2)=(\lambda-25)(\lambda^2+6)
-d_1(\lambda-1)-d_2(\lambda+1),
\qquad d_1,d_2\in[-75,75].
\]

The constant and linear coefficients check: the centered polynomial is lambda cubed minus 25 lambda squared plus 6 lambda minus 150. There is no product of d_1 and d_2.

For each fixed real lambda, independently varying d_1 and d_2 gives exactly the interval centered at (lambda-25)(lambda squared+6) with radius 75(|lambda-1|+|lambda+1|). This is an exact scalar Minkowski sum, not the result of substituting intervals into dependent polynomial coefficients. A zero in that interval is attained by some parameter pair because a continuous affine map sends this connected box onto the entire interval between its extrema. For real A and real lambda, singularity of lambda I-A supplies a nonzero real kernel vector, agreeing with the canonical definition.

All four displayed parameter pairs lie in their prescribed intervals, and the displayed eigenvectors are nonzero. Independent integer multiplication gives:

| lambda | (a,b) | v | A v = lambda v |
|---:|---|---|---|
| -3 | (-21,154) | (-4,2,1) | (12,-6,-3) |
| 0 | (-16,9) | (-1,-1,1) | (0,0,0) |
| 3 | (-146,29) | (4,1,2) | (12,3,6) |
| 25 | (-91,84) | (312,12,13) | (7800,300,325) |

The separator calculations also check exactly:

| lambda | Center | Radius | Exact determinant interval |
|---:|---:|---:|---|
| -1 | -182 | 150 | [-332,-32] |
| 1 | -168 | 150 | [-318,-18] |
| 12 | -1950 | 1800 | [-3750,-150] |

Every interval is strictly negative, so each separator is excluded for every admissible matrix, not merely at the midpoint or a selected sample. As a second check, this reviewer independently evaluated the uncentered determinant at all four endpoint pairs (a,b) for each separator; its minimum and maximum reproduced the same intervals. Endpoint zero, rounding, and interval-membership ambiguity play no role.

## Topological conclusion and limits

The included real numbers are ordered as -3<0<3<25, with the excluded numbers -1,1,12 lying strictly in the successive gaps. A connected subset of the real line containing two of the included points would contain every point between them. The relevant separator prevents this for each adjacent pair. Therefore these four points belong to four distinct connected components of the actual union of real eigenvalues.

A dimension-three matrix individually has only three eigenvalues counting algebraic multiplicity, but the witnesses come from different admissible matrices. That creates no contradiction: the conjecture concerns their union. Four components are enough to refute its universal bound. Neither tracing all eigenvalue branches nor finding the exact endpoints of those components is necessary. The proof does not establish a sharp replacement bound in general dimension, and no such result is needed to settle the stated conjecture negatively.

## Code and execution evidence

`verify_iv06` symbolically expands the exact characteristic polynomial, verifies parameter membership and all four integer eigenpairs, and computes the three determinant intervals with exact integers. Its tests match the manuscript. It does not use a floating-point eigensolver or numerical root finder. The fresh parent-run [exact_results.json](../exact_results.json) records all four eigenpairs and three separators as passing.

Independent standard-library arithmetic in this review rechecked the four matrix-vector products and all endpoint determinant values for the separators without importing the supplied verification functions. All passed. Here the finite integer data constitute the complete counterexample certificate, while the exact range and connectedness arguments prove why that certificate suffices; the result is not an inference from random tests.

## Primary-source comparison

The following primary sources were accessed on 2026-09-11:

- [Hladik, Daney, and Tsigaridas, *An algorithm for addressing the real interval eigenvalue problem*](https://www-sop.inria.fr/coprin/PDF/jcam2011.pdf), Section 1.2, published page 2716: it defines independent-entry interval matrices and their real eigenvalue union, then explicitly proposes the at-most-n compact-interval conjecture. The submitted counterexample matches this formulation directly.
- [The same authors, *Characterizing and approximating eigenvalue sets of symmetric interval matrices*](https://www-sop.inria.fr/coprin/PDF/CAMWA6430.pdf), Section 2, published page 3153: its family imposes A=A transpose, generally giving a proper subset of the independent-entry box. The ordered symmetric eigenvalue ranges yield n compact intervals. The submitted nonsymmetric example does not challenge that separate conclusion.

No source amendment or qualification is required for the counterexample. The exact canonical component-count claim is disproved; broader replacement bounds and priority remain outside this review.
