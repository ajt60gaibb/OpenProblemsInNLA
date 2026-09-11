# Draft title: RA-02 — the same-rank RPCholesky factor is exactly 2^r

> **HOLD: not cleared for posting.** The exact current RA-02 source and the full issue/PR exclusion audit must be checked first, especially omnibus PRs #6 and #32. This is a proposed negative resolution of the polynomial-factor question as described in the category listing, not a claim of repository acceptance or verified priority.

## Proposed result

For every integer \(r\ge1\),

\[
\sup_{A\succeq0,\;\tau_r(A)>0}
\frac{\mathbb E\operatorname{tr}R_r}{\tau_r(A)}=2^r,
\qquad
\tau_r(A)=\sum_{j>r}\lambda_j(A),
\]

where \(R_r\) is the residual after exactly \(r\) steps of standard randomly pivoted Cholesky, selecting a diagonal entry with probability proportional to its residual diagonal value.

Consequently no universal constants \(C>0\) and \(p\ge0\) give
\(\mathbb E\operatorname{tr}R_r\le Cr^p\tau_r(A)\) for all ranks and all positive-semidefinite inputs. The lower bounds already occur as limits of real, entrywise-positive, positive-definite matrices of order \(r+1\). The supremum is unchanged on positive-definite, unit-diagonal inputs if the dimension is unrestricted.

## Construction

Fix \(r\), set \(n=r+1\), and let \(0<t<1\). With one-based indices, define

\[
L_{ij}=\begin{cases}1&i=j,\\t^j/(i+j)&i>j,\\0&i<j,\end{cases}
\quad \epsilon=t^{n^2},\quad
A=L\operatorname{diag}(1,\epsilon,\ldots,\epsilon^r)L^{\mathsf T}.
\]

Then \(\tau_r(A)\sim\epsilon^r\), while the expected residual trace is asymptotic to \(2^r\epsilon^r\). Every square minor is nonzero for all sufficiently small positive \(t\), so the proof does not rely on an undefined zero-pivot limit.

## Proof outline

For an ordered pivot history with prefix sets \(S_s\), determinant cancellation gives the exact contribution

\[
\Pr(\text{history})\operatorname{tr}R_r
=\det A\prod_{s=0}^{r-1}\frac1{T_s(S_s)},
\quad
T_s(S)=\operatorname{tr}\bigl(A-A[:,S]A[S,S]^{-1}A[S,:]\bigr).
\]

Cauchy–Binet and explicit Cauchy prefix minors show
\(\epsilon^s/T_s(S)\to\mathbf1_{\{s+1\notin S\}}\).
Exactly \(2^r\) ordered histories satisfy all these prefix conditions: at position \(u\), the next label can be either of the two unused elements of \(\{1,\ldots,u,n\}\). The history sum is finite for each fixed \(r\). The matching universal upper bound is Chen–Epperly–Tropp–Webber, Lemma 5.5.

The attached manuscript supplies all intermediate lemmas, the eigenvalue normalization, and the unit-diagonal extension. Exact rational code independently enumerates actual pivot updates in small dimensions. At \(r=8\), \(t=1/100\), a retained-history certificate gives a ratio strictly greater than \(255.85420697\), compared with the sharp supremum \(256\).

## Attachments and limits

Attach `manuscript/sharp_random_pivoting.pdf` and the accompanying verification source/results. The same manuscript also gives the RPLU sharpness result relevant to RA-03.

This is an exact-arithmetic, same-rank worst-case statement. It does not settle RA-01: the small-dimensional example becomes exact after one additional pivot. No bounded-condition-number claim is made. The proof has been self-checked and tested with exact arithmetic, but has not yet undergone independent mathematical review.

Before posting, confirm the current RA-02 hypotheses, the absence of an already listed solution in **all** issue and PR states and comments, the repository's contribution format, and author/submitter attribution. If a prior solution is listed, do not submit this as an unresolved-problem resolution.
