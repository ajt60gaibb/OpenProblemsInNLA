# MI-16: exact maximum for one-exceptional-eigenvalue spectra

**Classification: USEFUL REDUCTION / LEMMA.** A complete proof for the spectral class below is provided. The arbitrary-spectrum repository problem is not resolved. Novelty relative to the permanent literature has not been established.

## Original target and scope

The canonical MI-16 README asks, for every integer n >= 1 and every list of nonnegative real eigenvalues lambda, for the exact value

\[
M_n(\lambda)=\max_{U\in\mathcal U_n}\operatorname{per}(U^*\operatorname{diag}(\lambda)U).
\]

Here the field is complex and the maximization includes every unitary matrix. This result handles precisely the lists (alpha,beta,...,beta), with alpha,beta >= 0. It does not assume alpha >= beta.

## Theorem

Put delta = alpha-beta. Then

\[
\boxed{M_n(\alpha,\beta,\ldots,\beta)=
\max_{1\le k\le n}\sum_{j=0}^{k}
\binom{k}{j}j!\,\beta^{n-j}\frac{\delta^j}{k^j}.}
\tag{1}
\]

A maximizing matrix is

\[
H_k=\beta I_n+\frac{\delta}{k}(J_k\oplus0_{n-k}),
\tag{2}
\]

for any k attaining (1). Thus only n explicitly evaluated polynomials are compared; (1) is not a restatement of the unitary optimization. Exponent-zero factors are 1, also when their base is zero.

If alpha >= beta, the maximum in (1) is attained at k=n. If beta=0, the formula becomes n! alpha^n/n^n. If alpha=beta, it becomes beta^n.

## Proof

Every Hermitian matrix with this spectrum has the form

\[
H=\beta I_n+\delta uu^*,\qquad u^*u=1.
\tag{3}
\]

This follows by choosing a unit eigenvector for the exceptional eigenvalue; when delta=0 any unit vector can be used. Conversely (3) has the required spectrum.

Set t_i=|u_i|^2. Then t belongs to the standard simplex. In the permanent expansion of (3), choose the rows on which the rank-one summand rather than the identity summand is used. If that set is S of size j, all rows outside S force their columns to be fixed. The remaining permutation is any permutation of S. Each such permutation contributes

\[
\beta^{n-j}\delta^j\prod_{i\in S}u_i\overline{u_{\sigma(i)}}
=\beta^{n-j}\delta^j\prod_{i\in S}t_i.
\]

There are j! such permutations. Therefore

\[
\operatorname{per}(H)=f(t):=
\sum_{j=0}^{n}j!\,\beta^{n-j}\delta^j e_j(t),
\tag{4}
\]

where e_0=1 and e_j is the elementary symmetric polynomial. Every point of the simplex is realized, by taking u_i=sqrt(t_i). Complex phases do not change (4).

We use the following elementary optimization lemma.

**Lemma.** Every real symmetric multiaffine polynomial f on the standard simplex has a maximizer whose positive coordinates are all equal.

**Proof of the lemma.** Continuity and compactness give a maximizer. Among all maximizers choose one with the smallest support. Fix any two positive coordinates x,y, keeping their sum s and all other coordinates fixed. Multiaffinity and symmetry give

\[
f=C+A(x+y)+Bxy=C+As+Bxy,
\]

where C,A,B depend only on the other coordinates. If B<0, replacing (x,y) by (s,0) strictly increases f, a contradiction. If B=0, that replacement preserves f and reduces support, also a contradiction. Thus B>0. For fixed s, xy has its unique maximum at x=y=s/2, so maximality forces x=y. This holds for every pair of positive coordinates. The one-coordinate case is immediate. This proves the lemma.

Apply the lemma to (4). On a support of size k, the positive coordinates are 1/k and

\[
e_j(t)=\binom{k}{j}k^{-j}\quad(0\le j\le k),
\]

with e_j=0 for j>k. Substitution gives (1), and the corresponding real unit vector gives (2).

When delta>=0, all coefficients of e_j in (4) are nonnegative. For fixed j<=k,

\[
\binom{k}{j}k^{-j}=\frac1{j!}\prod_{r=0}^{j-1}(1-r/k)
\]

is nondecreasing in k; the additional terms when k increases are nonnegative. Hence k=n is a maximizer. The beta=0 and alpha=beta formulas follow directly, including the all-zero spectrum. This completes the proof.

## Exact cautionary example

For n=3 and spectrum (0,1,1), the three candidate values are 0, 1/2, and 4/9. Thus M_3(0,1,1)=1/2, attained by

\[
\begin{pmatrix}1/2&-1/2&0\\-1/2&1/2&0\\0&0&1\end{pmatrix}.
\]

The uniform-support representative has permanent 4/9 and is not optimal. Therefore even this restricted class does not allow unconditional full-support/equal-diagonal maximization. This example is a reconstruction, not a claim of a new counterexample to the historical equal-diagonal conjecture.

## Remaining gap

For two or more genuinely independent exceptional eigendirections, the orbit is no longer parameterized by one simplex and its permanent is not the symmetric multiaffine polynomial (4). No arbitrary-spectrum formula is proved here.

## Sources

Canonical target: https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-16/README.md

README blob observed: `420630af16ff4118610f8b49acb4464a8e782510`.

The proof above is self-contained; it does not rely on an unverified optimizer assertion from the earlier handoff.
