# MI-27: projection reduction and a sharpness family

**Classification: USEFUL REDUCTION / LEMMA.** The universal coefficient-one upper bound remains unproved here. The statements below repair a specific missing step in the prior handoff and show rigorously why a universal coefficient below one cannot work.

## Exact original claim

For all integers n>=1 and complex positive definite A,B with tr(A+B)=1, put a=tr A, b=tr B. The target is

\[
\|[B,\log(A+B)]\|_1\le h(b),\qquad
h(t)=-t\log t-(1-t)\log(1-t),
\tag{1}
\]

using natural logarithms and the Schatten trace norm. Set h(0)=h(1)=0 by continuity.

## Theorem 1: exact projection equivalence

The original claim (1) in all dimensions is equivalent to the following claim:

For every positive definite S with tr S=1 and every orthogonal projection P (any rank, including 0 and n),

\[
\|[S^{1/2}PS^{1/2},\log S]\|_1
\le h(\operatorname{tr}(SP)).
\tag{2}
\]

No fixed value of b is imposed while making this reduction.

### Proof: original claim implies the projection claim

Fix S,P. For 0<epsilon<1/2 let

\[
K_\epsilon=\epsilon I+(1-2\epsilon)P,
\quad B_\epsilon=S^{1/2}K_\epsilon S^{1/2},
\quad A_\epsilon=S-B_\epsilon.
\]

The eigenvalues of K_epsilon belong to {epsilon,1-epsilon}, so both A_epsilon and B_epsilon are positive definite. Their sum is exactly S. Apply (1) and let epsilon tend to zero. The commutator, trace norm, trace, and h are continuous; S and log S stay fixed. This gives (2), including the endpoint ranks.

### Proof: projection claim implies the original claim

Fix S=A+B and K=S^{-1/2}BS^{-1/2}, so 0<K<I. In fact the following argument works for every 0<=K<=I.

Write the eigenvalues of K in decreasing order k_1>=...>=k_n>=0, set k_{n+1}=0, and let P_i project onto its first i orthonormal eigenvectors. Then

\[
K=\sum_{i=1}^n(k_i-k_{i+1})P_i+(1-k_1)0.
\tag{3}
\]

All coefficients are nonnegative and sum to one. Denote the resulting projections, including 0, by P_i with weights theta_i. Put B_i=S^{1/2}P_iS^{1/2} and b_i=tr B_i. Then B=sum theta_i B_i and b=sum theta_i b_i.

By linearity of the commutator, convexity of the trace norm, (2), and concavity of h,

\[
\|[B,\log S]\|_1
\le\sum_i\theta_i\|[B_i,\log S]\|_1
\le\sum_i\theta_i h(b_i)
\le h\!\left(\sum_i\theta_i b_i\right)=h(b).
\]

Concavity follows from h''(t)=-1/t-1/(1-t)<0 on (0,1), together with continuity at the endpoints. This proves the equivalence.

### Why the earlier trace-slice objection does not invalidate this proof

For a prescribed b, extreme points of {0<=K<=I : tr(SK)=b} need not all be projections. Already n=1, S=1, b=1/2 gives the singleton K=1/2. The argument above instead uses the full interval 0<=K<=I and permits b_i to vary. Jensen's inequality recombines the different right-hand sides. Claiming a projection reduction at fixed b without this distinction would be unjustified.

## Theorem 2: any valid universal coefficient is at least one

For 0<t<1/2 define

\[
S_t=\begin{pmatrix}1-t&0\\0&t\end{pmatrix},\qquad c_t=t(1-t),
\]

\[
B_t=t^2S_t+(1-2t^2)c_t
\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad A_t=S_t-B_t.
\tag{4}
\]

Both matrices are positive definite, tr(A_t+B_t)=1, and

\[
\lim_{t\downarrow0}
\frac{\|[B_t,\log S_t]\|_1}{h(\operatorname{tr}B_t)}=1.
\tag{5}
\]

### Proof

Let u=(sqrt(t),sqrt(1-t))^T and P=uu^T. Then P is a rank-one orthogonal projection and S_t^{1/2}PS_t^{1/2}=c_t J_2. Consequently

\[
B_t=S_t^{1/2}\bigl(t^2I+(1-2t^2)P\bigr)S_t^{1/2}.
\]

The middle factor has eigenvalues t^2 and 1-t^2, both strictly between zero and one. This proves strict positivity of A_t and B_t.

The two off-diagonal entries of B_t equal d_t=(1-2t^2)t(1-t). Thus

\[
\|[B_t,\log S_t]\|_1
=2d_t\log\frac{1-t}{t},
\qquad b_t:=\operatorname{tr}B_t=t^2+2d_t.
\tag{6}
\]

Indeed the commutator is a real skew-symmetric 2-by-2 matrix with off-diagonal magnitude d_t log((1-t)/t), so its two singular values equal that magnitude.

Now b_t/(2t)->1 and

\[
\frac{2d_t\log((1-t)/t)}{2t\log(1/t)}\longrightarrow1.
\]

For b->0, -(1-b)log(1-b)=b+O(b^2), whence h(b)/(b log(1/b))->1. Together with b_t/(2t)->1 this gives h(b_t)/(2t log(1/t))->1 and proves (5).

Therefore every c<1 fails in the inequality ||[B,log(A+B)]||_1<=c h(b) for sufficiently small t, with A,B satisfying the original strict assumptions. This is a lower-bound/sharpness result, not a counterexample to coefficient one.

## Remaining gap

Proving (2) uniformly for arbitrary S and arbitrary-rank P, or finding a counterexample to it, remains necessary. Neither Theorem 1 nor Theorem 2 supplies that upper bound.

## Source

Canonical target: https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-27/README.md

README blob observed: `d7d202d2c9b313d426569547c5466e059a430c0e`.

These proofs use only finite-dimensional spectral calculus, convexity, and elementary limits. Historical novelty is not claimed.
