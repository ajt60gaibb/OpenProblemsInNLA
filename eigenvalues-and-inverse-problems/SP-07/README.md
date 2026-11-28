# SP-07 — The sharp spectral-matching constant for normal matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-11-28  

**Rating rationale:** Extreme reflects a longstanding sharp-constant problem beyond the false constant-one conjecture; community impact is eigenvalue matching and perturbation theory for normal matrices.

## Supporting completion barriers and stationary model — 14 September 2026

Sidney Holden (Center for Computational Biology, Flatiron Institute, Simons Foundation). The [report](../../references/holden-sp-continuations-2026-09-14/SP-07/report.pdf), Sections 2–7, proves odd-polygon completion barriers and solves a stationary two-line variational model. The formal quotient near 1.0373054 is not a finite normal-matrix lower bound. The inherited order-193 rational certificate was rerun by both exact positivity methods. Neither this continuation nor that certificate determines the unrestricted sharp constant; status stays Open.

See the [independent informal Codex AI-agent review](../../references/holden-sp-continuations-2026-09-14/SP-07/independent-review.md) for the exact audited scope and checks, and the [submission record](../../references/holden-sp-continuations-2026-09-14/README.md) for verified affiliation, original materials and reproduction details. No full resolution, external human peer review, formal verification or historical novelty is claimed. No Lean verification was performed.

## Reviewed continuation — 13 September 2026

Sidney Holden (Center for Computational Biology, Flatiron Institute, Simons Foundation) supplies an exact rational seven-dimensional normal pair proving $`C_{\rm normal}>1.03077`$; see the [continuation report](../../references/holden-continuations-2026-09-13/SP-07/report.pdf), Section 3, Theorem 3.1. A Hall obstruction supplies the matching lower bound and exact positive-definiteness certifies the full operator-norm upper bound. The report also proves restricted dimension reductions in Sections 6–8.

Status remains **Open**: this certified lower bound and the restricted reductions do not determine the exact universal constant or a matching upper bound. No global extremality or finite-dimensional stabilization is asserted.

The [independent informal Codex AI-agent review](../../references/holden-continuations-2026-09-13/verification/SP-07/review.md) records its accepted scope and checks. [Submission, original package, reproduction and verified affiliation](../../references/holden-continuations-2026-09-13/README.md). This is not external human peer review or formal verification; no Lean verification was performed.

## Supporting subclass lemma — 12 September 2026

Sidney Holden (Center for Computational Biology, Flatiron Institute, Simons Foundation) supplies [a proof of the sharp constant-one bound](../../references/holden-spectral-2026-09-12/SP-07/result.md) when at least one normal input has at most two distinct eigenvalues, using [Theorem 1](../../references/holden-spectral-2026-09-12/SP-09/proof.md). This passed an [independent informal Codex AI-agent audit](../../references/holden-spectral-2026-09-12/verification/SP-09-SP-07-SP-03-review.md). It gives no new global bound or value for $`C_{\rm normal}`$; status remains Open. [Submission and verified affiliation](../../references/holden-spectral-2026-09-12/README.md). No novelty, external human peer review or formal verification is claimed.


## Problem statement

For normal matrices $`A,B\in\mathbb C^{n\times n}`$, list their eigenvalues
$`\alpha_1,\ldots,\alpha_n`$ and $`\beta_1,\ldots,\beta_n`$ with algebraic
multiplicity. Define the bottleneck matching distance

```math
d_\infty(A,B)=\min_{\pi\in S_n}\max_{1\le j\le n}
|\alpha_j-\beta_{\pi(j)}|,
```

where $`S_n`$ is the permutation group. Determine the exact value of

```math
C_{\rm normal}=\sup_{n\ge2}\ \sup_{\substack{A,B\in\mathbb C^{n\times n}\ \mathrm{normal}\\ A\ne B}}
\frac{d_\infty(A,B)}{\|A-B\|_2}.
```

Here normal means $`AA^*=A^*A`$, and $`\|\cdot\|_2`$ is the spectral norm.
The target is a single sharp constant valid in every dimension. Equivalently,
find the smallest $`C`$ for which $`d_\infty(A,B)\le C\|A-B\|_2`$ for all such
pairs, with matching sharpness evidence. The conjectured value $`C=1`$ has
already been refuted; it is not the question being posed.

## Improved singular-value bound — 2026-11-28

**Partial result (AI-derived).** Write $`s_1\ge s_2\ge\cdots`$ for the
singular values of $`A-B`$ and put $`r_n=\lfloor(n+1)/2\rfloor`$. Then

```math
d_\infty(A,B)^2\le s_1^2+\frac12\sum_{i=2}^{r_n}s_i^2.
```

This halves the contribution of the smaller singular values in [Tang's truncated bound, Theorem 1.1](https://arxiv.org/html/2609.09177v2).
For the constant restricted to order $`n`$, it gives
$`C_n\le \sqrt{(r_n+1)/2}`$. This improves the minimum of Tang's bound
and the classical dimension-independent bound of $`2.9038872828`$ in
orders 3 through 30. The argument below also
gives $`C_3\le\sqrt{7/5}`$. The exact dimension-independent constant
$`C_{\rm normal}`$ remains open.

**Proof.** Let $`\delta=d_\infty(A,B)>0`$ and $`m=\|A-B\|_2`$. In
the bipartite graph that joins eigenvalue labels at distance less than
$`\delta`$, there is no perfect matching. Hall's theorem provides two
sets of labels with combined size $`n+1`$ and every cross distance at
least $`\delta`$. Let $`U,V`$ be their spans in orthonormal eigenbases of
$`A,B`$, respectively. Swap the two matrices if necessary so that
$`\dim U=r\le \dim V`$. Then $`r\le r_n`$ and there is a common unit
vector $`z\in U\cap V`$.

Write $`P_U,P_V`$ for the orthogonal projections and put
$`C=P_U(A-B)|_V`$ and $`H=\sum_{i=1}^r s_i^2`$. Let $`\gamma`$ be the
norm of $`P_U`$ from $`V\cap z^\perp`$ to $`U\cap z^\perp`$.
In the chosen eigenbases the entries of $`C`$ are the corresponding
cross eigenvalue differences times the entries of $`P_U|_V`$.
The common direction contributes one to the squared Frobenius norm of
$`P_U|_V`$, and its orthogonal part contributes at least $`\gamma^2`$.
Thus

```math
\|C\|_F^2\ge\delta^2(1+\gamma^2).
```

Set $`a=\|(I-zz^*)Az\|_2`$ and $`b=\|(I-zz^*)Bz\|_2`$. The
average of $`|\alpha_i-\beta_j|^2`$ with the independent weights
given by the squared coordinates of $`z`$ in the two eigenbases is
$`|z^*Az-z^*Bz|^2+a^2+b^2`$, at least $`\delta^2`$. The inner
product of the two orthogonal components of $`Az,Bz`$ has modulus
at most $`\gamma ab`$. Also, projecting $`(A-B)z`$ onto $`U^\perp`$
leaves only the contribution from $`Bz`$. It follows that

```math
m^2\ge\delta^2-2\gamma ab,\qquad m^2\ge(1-\gamma^2)b^2.
```

For an orthonormal basis of $`U`$ starting with $`z`$, the sum of
squared norms of $`(A-B)^*`$ on the basis is at most $`H`$ by the
Ky Fan maximum principle. Computing $`\|C^*\|_F^2`$ projects each
of these vectors onto $`V`$. On the first vector the projection loses
squared norm at least $`(1-\gamma^2)a^2`$, since $`B^*z\in V`$ and
normality gives $`\|(I-zz^*)A^*z\|_2=a`$. Therefore

```math
H\ge\delta^2(1+\gamma^2)+(1-\gamma^2)a^2.
```

The desired estimate holds if $`\delta\le m`$ since $`H\ge m^2`$,
and the inequalities above cover $`\gamma=0`$ and $`\gamma=1`$.
In the remaining case set $`D=\delta^2-m^2>0`$. The first two
inequalities give $`a^2\ge (1-\gamma^2)D^2/(4\gamma^2m^2)`$. By
the arithmetic–geometric mean inequality,

```math
\gamma^2m^2+\frac{(1-\gamma^2)^2D^2}{4\gamma^2m^2}
\ge (1-\gamma^2)D.
```

Substituting into the bound for $`H`$ gives $`H\ge\delta^2+D`$,
which proves the result with $`r`$ in place of $`r_n`$.

For $`n=3`$ either $`r=1`$, which gives $`\delta\le m`$, or both
subspaces have dimension two. In the latter case project the two
basis vectors of $`V`$ starting with $`z`$ onto $`U`$ after applying
$`A-B`$. This gives the second Frobenius bound
$`2m^2\ge\delta^2(1+\gamma^2)+(1-\gamma^2)b^2`$.
Averaging it with the first bound and using
$`D\le 2\gamma ab\le\gamma(a^2+b^2)`$ shows

```math
\frac{m^2}{\delta^2}\ge
\frac{1+\gamma^2+c}{2+c},\qquad c=\frac{1-\gamma^2}{2\gamma}.
```

The right-hand side is at least $`5/7`$, since the equivalent
inequality $`7\gamma^3-\gamma^2-3\gamma+1\ge0`$ has minimum
$`4/49`$ over $`[0,1]`$, attained at $`3/7`$. This yields the stated
order-three bound.

## Why it matters

This is a sharp conditioning question for the complete spectrum of a normal
matrix. Matching counts repeated eigenvalues, so a Hausdorff-distance estimate
that ignores multiplicity does not answer it.

## References

R. Bhatia, [*Perturbation Bounds for Matrix Eigenvalues*](https://epubs.siam.org/doi/10.1137/1.9780898719079.ch9), SIAM, 2007, Chapter IX, pp. 154–155; the question is restated as Problem 27 in X. Zhan, [*Open problems in matrix theory*](https://math.ecnu.edu.cn/~zhan/papers/ZhanICCM.pdf), §21, pp. 12–13. P. Šemrl, [*Geometrical techniques in linear algebra*](https://indico.ictp.it/event/a08167/session/73/contribution/52/material/0/0.pdf), ICTP lecture notes, 2009, p. 10, Theorem 5 and the following open question. J. A. Holbrook, [*Spectral variation of normal matrices*](https://doi.org/10.1016/0024-3795(92)90047-E), LAA 174 (1992), 131–144.

## Earlier status check — 2026-09-08

The cited sources distinguish the unresolved sharp constant from Holbrook's
counterexample to one. They give $`1< C_{\rm normal}<3`$. A. Parusiński and A. Rainer,
[*Eigenvalue stability of Hermitian and normal matrices*](https://arxiv.org/abs/2603.23056),
v1 (2026), Proposition 3.4, still states the classical universal bound with
$`1< C<3`$; it does not determine the sharp constant. Searches for
`sharp spectral variation constant normal matrices`, `spectral variation best
possible constant`, and 2025/2026 follow-ups found no exact value. The explicit
open-question sources are historical; the recent bound is context, not an
explicit reaffirmation of openness. This is a bounded literature check.

## Audit update — 2026-09-10

The [2026 spectral perturbation manuscript](https://arxiv.org/pdf/2603.23056), Proposition 3.4, still uses a universal constant strictly between 1 and 3 rather than determining the optimum. Sharp-normal-spectral-matching searches found no exact value. This supports the retained open verdict alongside the historical lower-bound examples cited above; the old constant-one statement is already false and is not the target here.
