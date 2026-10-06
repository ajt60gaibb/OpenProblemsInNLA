# Proposed Gaussian-specific overcrowding proof: request for independent review

This is a mathematical proposal by `/root`, not an implemented or certified
probabilistic theorem. It aims to prove the exact A3 bound without importing
Nguyen's stronger general-iid theorem.

For n>j≥4, put q=ceil(j/4), r=j+1-2q, m=n-2q. Then q,r≥1,
r≤m, and 2rq≥j²/4 (equivalently qr≥j²/8). Let R be the first m
rows of the square iid standard Gaussian G, and W=R Rᵀ. W is invertible a.s.

If the source's one-based singular value sigma_(n-j)(G)≤t, row-deletion
interlacing gives sigma_(n-j)(R)≤t. Hence W^-1 has at least
m-(n-j)+1=r eigenvalues≥t^-2. Its rth elementary symmetric polynomial
is ≥t^(-2r). The sum of its r×r principal minors equals this polynomial.
With N=binom(m,r), some principal minor D_S is therefore ≥t^(-2r)/N.

For a fixed r-row subset S, condition on the other m-r rows. The inverse
Gram principal block is the inverse of the selected rows' residual Gram
matrix in dimension n-(m-r)=j+1. The selected rows remain independent
standard Gaussians in that orthogonal complement. Bartlett/Gram–Schmidt
then gives the exact negative determinant moment

E[D_S^q] = product_(a=0..r-1) product_(b=1..q) (j+1-a-2b)^(-1).

Every residual dimension j+1-a is ≥2q+1, so each a-factor is at most
1/(2q-1)!! ≤1/q! ≤(e/q)^q. Thus E[D_S^q]≤(e/q)^(rq).
All conditional projection, block inverse, determinant-factorization,
integrability and moment assertions in this paragraph require proofs.

By Markov and a finite union over S,

P{sigma_(n-j)(G)≤t} ≤ N * (e/q)^(rq) * N^q * t^(2rq).

The sharp combinatorial bound N≤(em/r)^r≤(en/r)^r is essential;
replacing it by n^r inside the Markov threshold would lose a factor of j.
Set t=c*j*theta/sqrt(n), with 0<theta≤1 and c=1/(4e). Then

(e/q)^(rq) N^q t^(2rq)
 ≤ (e² c² j²/(qr))^(rq) theta^(2rq)
 ≤ (1/2)^(rq) theta^(2rq)
 ≤ theta^(j²/4).

Finally N≤n^r≤n^(j+1), yielding exactly the reviewed A3 target
P{sigma_(n-j)(G)≤c*j*theta/sqrt(n)}≤n^(j+1)*theta^(j²/4).
The threshold is positive, so inversion reverses inequalities legitimately.
The singular Gram exceptional set is null, not an extra failure probability.

Needed supporting modules: actual Gaussian block-regression/Bartlett moments,
min–max row interlacing, elementary symmetric/principal-minor identity,
integer q/r arithmetic, factorial and binomial bounds. This proposal changes
the proof route only, not the original or intermediate A3 target.
