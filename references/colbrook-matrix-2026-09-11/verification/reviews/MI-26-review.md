# MI-26 independent proof review

**Verdict: PASS — complete negative resolution for the exact real-valued concave function class.**

Review date: 11 September 2026. Reviewer: independent agent `/root/review_matrix_exact`. Read the full original `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-26.tex`, preamble, relevant bibliography, and `matrix-inequalities-and-norms/MI-26/README.md`. Original and canonical files were not edited.

## Original full-file identity

SHA-256 of the full original TeX decoded as UTF-8, normalized to LF, and re-encoded without trimming: `3ca2f7dc760b25d45f24706336acf1adf6af790864ea3fad7526c12046466ea0`. Original and normalized lengths: 2,385 bytes; no bare CR. The hash covers the theorem, full proof including the explicit PD construction, and the function-class remark.

## Function class and source fidelity

The canonical question permits all real-valued concave functions on the half-line with f(0) >= 0, without global nonnegativity or monotonicity, and PSD A,B. It asks whether there exist U,V for every such triple. The polynomial f(t) = t - t^2 has f'' = -2, is real-valued throughout the domain, and has f(0) = 0. Its negative values for t > 1 are allowed.

The actual [Audenaert–Kittaneh Problem 5, following equation (11)](https://arxiv.org/html/1201.5232) explicitly asks whether monotonicity can be removed while retaining concavity and f(0) >= 0. [Bourin–Lee Remark 3.13](https://arxiv.org/html/1109.2384) asks to remove the monotonicity assumption from their Theorem 3.1. Neither question adds global nonnegativity. Earlier norm inequalities for nonnegative functions in the same source are different statements. This source distinction was independently checked and is essential to the verdict.

## PSD construction and exclusion of every unitary pair

P is a rank-one orthogonal projection. Q = vv^T with v = (3/5,4/5)^T, so Q is also a rank-one orthogonal projection. Consequently f(P) = f(Q) = 0, and both unitary conjugates remain zero for all U,V, including complex unitaries.

Exact multiplication gives

\[
f(P+Q)=-(PQ+QP)=\frac1{25}\begin{pmatrix}-18&-12\\-12&0\end{pmatrix}.
\]

Its trace is -18/25 and its determinant is -144/625. Its eigenvalues are 6/25 and -24/25; direct multiplication verifies eigenvector (1,-2)^T for the positive eigenvalue. Thus f(P+Q) is not negative semidefinite. This excludes every candidate U,V, rather than merely testing selected bases.

## Explicit PD version

The second construction uses epsilon = 1/20 exactly. Each A = P + epsilon I and B = Q + epsilon I has positive eigenvalues 21/20 and 1/20. Applying the polynomial gives eigenvalues -21/400 and 19/400; hence each f(A), f(B) is bounded above by (19/400)I, even though it is not PSD. Unitary conjugation preserves this order bound and summing gives

\[
Uf(A)U^*+Vf(B)V^*\preceq (19/200)I
\]

for all complex unitaries. Separately, P+Q has eigenvalues 8/5 and 2/5. The scalar perturbation by 1/10 shifts these to 17/10 and 1/2 for A+B. Therefore f(A+B) has eigenvalues -119/100 and 1/4. Domination by any proposed right side would force its largest eigenvalue to be at most 19/200, contradicting 1/4 > 19/200. The resulting positive scalar gap is 31/200.

The independent Fraction script checked the matrix polynomial, projection identities, all listed eigenvalues by their characteristic determinants, the displayed eigenvector, and the scalar comparison. No numerical eigensolver or continuity assumption is needed for this explicit PD witness.

## Remark and limits

The final remark is correct: if a concave function on [0,infinity) has a negative secant slope between x < y, concavity bounds every subsequent secant slope from y above by that negative number. Its values must eventually become negative. A globally nonnegative concave function is therefore nondecreasing; the present f is outside that narrower class.

No material gap was found. This proof settles the exact canonical universal statement and its PD-input restriction, but not a differently restricted function class. The audit does not certify historical novelty or priority; source checking was bounded. This is independent agent review, not external human peer review or formal verification. Supplemental exact arithmetic is retained in `independent_exact_counterexamples.py`.
