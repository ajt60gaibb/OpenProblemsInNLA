# Independent full-source review: TR-15

Date: 2026-09-11. Verdict: **PASS**, an exact counterexample to the canonical universal inheritance assertion. Recommended status: **Solved (disproved)**. The counterexample satisfies its premise with all existing real H-eigenvalues strictly positive, and the premise is additionally shown to be nonvacuous.

## Reviewed source and target

I read the complete `references/colbrook-unclaimed-2026-09-11/manuscripts/TR-15.md`, including its proposition, optional existence argument, scope, provenance, and references, and compared the actual `tensor-computations/TR-15/README.md`. The final reviewed text has complete UTF-8, CRLF-to-LF, no-trimming SHA256:

`31aaf87084303a6de0ef380270c973719efa027c6131c76b27a02cb489a1fa74`

Locators: counterexample at line 11; proposition at line 24; nonvacuous-premise argument at line 39; scope at line 52; references at line 58. During review the author corrected the editorial phrase “order-four Hankel matrix” to “4 by 4 Hankel matrix”; the final full source was reread and the hash above includes that correction. No mathematical change or further correction is needed. This reviewer did not edit the manuscript or canonical files.

The canonical parameters m=3, q=2, n=2 meet every required inequality and parity constraint. The lower-order tensor dimension is `q(n-1)+1=3`, its order is 3, the higher-order tensor dimension is 2, and its order is `qm=6`. Both need generating-vector length seven: `3(3-1)+1=6(2-1)+1=7`. Both therefore use exactly the same h_0 through h_6; no padding or different truncation has been substituted.

## Primary source and conventions

I accessed [Ding–Qi–Wei, author's journal PDF](https://www.polyu.edu.hk/ama/staff/new/qilq/BIT-DQW.pdf) on 2026-09-11. Its final Section 4 (PDF page 21) states the third inheritance conjecture and explicitly leaves the odd-lower-order case unresolved. Its initial definitions use zero-based Hankel indices and componentwise `(s-1)`st powers in the H-eigenvalue equation. The manuscript's one-based index formulas subtract the order and are exactly equivalent. The source distinguishes the earlier even-lower-order result and the associated-positive-semidefinite-matrix hypothesis. [Journal DOI](https://doi.org/10.1007/s10543-016-0622-0).

The companion [Qi primary preprint](https://arxiv.org/pdf/1310.5470) was also accessed for the associated-Hankel background; the counterexample proof does not depend on a sufficiency theorem about strong or complete Hankel tensors. This review verifies mathematical correctness and source scope, not novelty or a claim of first discovery.

## All contraction and eigenvalue checks

The first slice of A is the symmetric matrix

`[[2,0,1],[0,1,0],[1,0,2]]`.

Its quadratic form is exactly `2x_1^2+x_2^2+2x_1x_3+2x_3^2`, equal to `(x_1+x_3)^2+x_1^2+x_2^2+x_3^2`. Thus it is strictly positive for every nonzero real x; equivalently its eigenvalues are 1, 1 and 3. For any real H-eigenpair of the order-three tensor, the first equation reads this positive quantity equals `lambda x_1^2`. It rules out x_1=0, then forces lambda>0. This proves a universal statement about **all** real H-eigenpairs, including ones not constructed or enumerated. It is not a numerical lower bound for sampled eigenvalues. Zero is excluded as well as negative eigenvalues.

For B and v=(0,1), each of its two contractions has exactly one surviving summand: all five contracted indices must be 2. The uncontracted first index i gives generator index `i+5*2-6=i+4`; hence the two entries are h_5 and h_6, respectively 0 and -1. Since the H-eigenvector power is now five, `v^[5]=(0,1)`, so `Bv^5=-v^[5]` exactly. The vector is real and nonzero, and lambda=-1 is a real negative H-eigenvalue.

As an independent check directly from the generator rather than from the printed formulas, I expanded all 27 entries of A using exact integer arithmetic and collected all three contraction polynomials. They are precisely:

- `(Ax^2)_1 = 2x_1^2+x_2^2+2x_1x_3+2x_3^2`;
- `(Ax^2)_2 = 2x_1x_2+4x_2x_3`;
- `(Ax^2)_3 = x_1^2+2x_2^2+4x_1x_3-x_3^2`.

I also independently contracted all 64 entries of B at v=(0,1), obtaining (0,-1). These finite exact calculations check every entry and indexing convention of this explicit example. The logical proof of positivity for all A eigenpairs is the positive-definite quadratic identity, not the finite calculation alone.

## Optional existence argument

For x=(1,0,t), the first equation gives `lambda=2+2t+2t^2`; the second is identically zero on both sides. Substituting into the third gives

`1+4t-t^2 = (2+2t+2t^2)t^2`,

equivalent to `2t^4+2t^3+3t^2-4t-1=0`, exactly as printed. Its values at 0 and 1 are -1 and 2. Continuity supplies a real root strictly between them. The resulting vector has first coordinate one, and lambda is positive. Thus A actually has a real H-eigenpair. Existence is not needed to negate the implication under the literal “no negative H-eigenvalues” premise, but the manuscript correctly supplies it and does not confuse odd-order polynomial positivity with H-eigenvalue positivity.

## Scope and final verdict

The associated Hankel matrix for the seven generators is 4 by 4, with entries h_(i+j-2); its bottom-right diagonal entry is h_6=-1. It is not positive semidefinite, so a theorem assuming an associated positive-semidefinite matrix is inapplicable. Likewise, the lower tensor order is odd, so the even-lower-order inheritance theorem is not contradicted. The polynomial value of B at (0,1) is h_6=-1, consistently with its exhibited H-eigenpair.

The proposition disproves the universal canonical conjecture by a fully admissible instance. There is no remaining case needed to answer that conjecture negatively. The manuscript does not claim that every odd-order instance fails or classify all generators for which inheritance succeeds. Its statements concerning prior incomplete archives and the provenance of the new coefficients are submission history, not mathematical premises of the proof; this review does not certify missing earlier materials or human authorship. The final source's main proposition, supplementary IVT argument, and scope claims all pass.
