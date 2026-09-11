# Draft title: RA-03 — a 2-by-2 counterexample, and sharpness of 4^r for RPLU

> **HOLD: not cleared for posting.** The exact current RA-03 source and the complete issue/PR exclusion audit must be checked first, especially omnibus PRs #6 and #32. This is a proposed negative resolution, not a claim of repository acceptance or verified priority.

## A complete counterexample to the literal 2^r bound

Take

\[
A=\begin{pmatrix}2&1\\1&2\end{pmatrix},\qquad r=1.
\]

The singular values are \(3\) and \(1\), hence \(\|A-A_1\|_F^2=1\). Standard RPLU samples an entry with probability \(|A_{ij}|^2/\|A\|_F^2\), where \(\|A\|_F^2=10\), and performs the rank-one cross update.

Each of the two diagonal pivots has probability \(2/5\) and leaves one residual entry of magnitude \(3/2\). Each of the two off-diagonal pivots has probability \(1/10\) and leaves one residual entry of magnitude \(3\). Therefore

\[
\mathbb E\|B_1\|_F^2
=2\left(\frac25\cdot\frac94\right)
 +2\left(\frac1{10}\cdot9\right)
=\frac{18}{5}
>2\|A-A_1\|_F^2.
\]

This is a real, positive-definite, entrywise-positive counterexample with exact rational arithmetic. Dividing the matrix by two gives a unit-diagonal counterexample with the same error ratio. There is no Monte Carlo estimate, limiting argument, or numerical singular-value computation in this calculation. The conjectured improvement after Theorem 3 of Gilles–Wilber explicitly concerns the **squared** Frobenius error.

## Stronger result: 4^r is the sharp worst-case factor

The accompanying manuscript proves, for every integer \(r\ge1\),

\[
\sup_{A:\,\|A-A_r\|_F>0}
\frac{\mathbb E\|B_r\|_F^2}{\|A-A_r\|_F^2}=4^r.
\]

The lower-bound matrices are the same real SPD family used for the RPCholesky result:
\(A=L\operatorname{diag}(1,\epsilon,\ldots,\epsilon^r)L^{\mathsf T}\),
with \(n=r+1\), \(L_{ii}=1\), \(L_{ij}=t^j/(i+j)\) for \(i>j\), and \(\epsilon=t^{n^2}\).
For fixed \(r\) and \(t\downarrow0\), the squared-error ratio tends to \(4^r\).
Thus even \(C2^r\), or \(q(r)2^r\) with a fixed polynomial \(q\), cannot be a universal factor. The known upper bound is Gilles–Wilber, Theorem 3.

For an ordered row/column history, squared pivot determinants cancel against the final residual entry. After normalization, each history contribution has a limit of zero or one. Exactly \(2^r\) row histories and \(2^r\) column histories survive, giving \(4^r\) pairs. This factorization concerns the limiting indicators; the proof does **not** assume independent row and column sampling by RPLU.

A replication argument also transfers the supremum to positive-definite, unit-diagonal inputs of unrestricted dimension. At \(r=8\), \(t=1/100\), an exact finite certificate gives a squared-error ratio greater than \(65461.37522779\), compared with the sharp supremum \(65536\).

## Attachments and review

Attach `manuscript/sharp_random_pivoting.pdf`, `verification/verify_ra03_2x2.py`, and the remaining verification source/results. The rank-one counterexample can be checked separately from the general theorem.

These are exactly \(r\)-pivot, rank-\(r\) comparisons. They do not concern the expectation of the unsquared Frobenius norm, a different normalization, nor do they resolve an oversampling question. The proof is self-checked but has not yet undergone independent mathematical review.

Before posting, verify the current RA-03 statement, all issue/PR states and comments, linked solution attachments, the repository contribution format, and author/submitter attribution. If a prior solution is listed, do not submit this as an unresolved-problem resolution.
