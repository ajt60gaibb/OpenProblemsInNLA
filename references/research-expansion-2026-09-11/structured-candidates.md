# Structured-matrix candidate audit — 2026-09-11

These are source checks for the new search, not additional canonical entries.

## S1. Trace-norm-small non-Hermitian perturbations

Let $H_n=H_n^*\in\mathbb C^{n\times n}$, and let $f:[0,1]\to\mathbb R$
be measurable. Write $\{A_n\}\sim_\lambda f$ when

$$\lim_{n\to\infty}\frac1n\sum_{j=1}^n F(\lambda_j(A_n))=
\int_0^1 F(f(t))\,dt\qquad(F\in C_c(\mathbb C)),$$

with eigenvalues counted with algebraic multiplicity. For arbitrary complex
$E_n$, is

$$\{H_n\}\sim_\lambda f,\qquad
\|E_n\|_*:=\sum_j\sigma_j(E_n)=o(n)
\quad\Longrightarrow\quad \{H_n+E_n\}\sim_\lambda f?$$

No boundedness of either sequence in spectral norm is imposed.

Source: Barbarino–Serra-Capizzano, *Non-Hermitian perturbations of Hermitian
matrix-sequences and applications to the spectral analysis of the numerical
approximation of partial differential equations*, NLAA 27 (2020), e2286,
[DOI](https://doi.org/10.1002/nla.2286),
[author PDF](https://giovannibarbarino.github.io/doc/articles/NHperturbation.pdf),
§6, Conjecture 1, printed p.29. Theorem 1 proves the stronger hypothesis
$\|E_n\|_F=o(\sqrt n)$; Corollary 3 covers trace-norm $o(n)$ with a
uniformly bounded perturbation. The weaker trace-norm condition need not
imply the Frobenius condition.

Barbarino's [arXiv:1808.05555v1](https://arxiv.org/abs/1808.05555v1),
Conjecture 1, Lemmas 4.1–4.2, records equivalent formulations and a related
converse (Conjecture 2). Do not count its various GLT/diagonal formulations as
separate problems. The downloaded PDF has a May 25, 2021 internal date while
the arXiv version identifier remains v1 from 2018; cite the journal statement
as primary. The converse is not needed for admission of S1.

Later scope check: Barbarino–Garoni, *GLT sequences and normal matrices*,
ELA 41 (2025), 1–20,
[Theorem 3.2](https://journals.uwyo.edu/index.php/ela/article/download/8929/6949/23285),
requires much smaller perturbations when the perturbed matrix is not normal;
it does not prove S1. Primary author publication list and exact-title,
author/conjecture, trace-norm/spectral-distribution and 2026 searches found no
full proof or counterexample on September 11, 2026. This is bounded evidence,
not exhaustive certification. Existing SP entries concern finite-dimensional
matching, subspace angles, or different Toeplitz properties, not S1.

## S2. Widom's canonical Toeplitz eigenvalue distribution conjecture

For $a\in C(\mathbb T;\mathbb C)$, put
$a_k=(2\pi)^{-1}\int_0^{2\pi}a(e^{it})e^{-ikt}\,dt$ and
$T_n(a)=(a_{j-k})_{j,k=0}^{n-1}$. Suppose $a$ is the continuous boundary
value of no holomorphic function on any annulus $r<|z|<1$ with $0<r<1$,
and of no holomorphic function on any annulus $1<|z|<R$ with $R>1$.
The conjectured conclusion is

$$\lim_{n\to\infty}\frac1n\sum_{j=1}^n F(\lambda_j(T_n(a)))
=\frac1{2\pi}\int_0^{2\pi}F(a(e^{it}))\,dt
\qquad(F\in C_c(\mathbb C)).$$

The extension must extend continuously to the unit circle with boundary value
$a$. Multiplicities are algebraic. The conjecture gives a necessary condition
for failure of canonical distribution, not a converse saying every analytic
symbol fails. Distinct from SP-06's all-orders real-spectrum target and MF-21's
individual-eigenvalue expansion threshold.

Primary explicit restatement: Bogoya–Böttcher–Grudsky, *Asymptotics of
individual eigenvalues of a class of large Hessenberg Toeplitz matrices*,
OTAA 220 (2012), 77–95,
[author manuscript](https://www.math.cinvestav.mx/~grudsky/Papers/116.pdf),
§1, p.2, immediately after (1.1). Original source cited there is Widom,
*Eigenvalue distribution of nonselfadjoint Toeplitz matrices and the asymptotics
of Toeplitz determinants in the case of nonvanishing index*, OTAA 48 (1990),
387–421; the 1994 Widom expository article *Eigenvalue distribution for
nonselfadjoint Toeplitz matrices*, OTAA 71, 1–8, also discusses it.

Modern reaffirmation: Bogoya et al., *Matrix-less methods for the spectral
approximation of large non-Hermitian Toeplitz matrices: A concise theoretical
analysis and a numerical study*, NLAA 31 (2024), e2545,
[DOI/full text](https://onlinelibrary.wiley.com/doi/full/10.1002/nla.2545),
introduction before Theorem 1. This explicitly says the conjecture is unsolved
and gives the Tilli-class sufficient case: essential range has empty interior
and connected complement. The 2022 Basor–Böttcher–Ehrhardt survey
[§4](https://www.ams.org/journals/bull/2022-59-02/S0273-0979-2021-01758-7/viewer/)
describes Widom's nonsmooth Jordan-curve cases. The 2024 page's indexed full
text was accessible; direct retrieval sometimes timed out.

On September 11, 2026, searched Widom/canonical distribution/annulus,
nonselfadjoint Toeplitz/conjecture/2026, and proof/counterexample combinations.
No full resolution was found. Other results called the Widom conjecture
(Toeplitz determinant trace asymptotics and random-matrix questions) are not
resolutions of this statement.

## Excluded leads

- Barbarino–Cicone, *Conjectures on spectral properties of ALIF algorithm*,
  [arXiv:2009.00582v2](https://arxiv.org/abs/2009.00582v2), Theorem 4.1 proves
  the earlier spectral-distribution conjecture; §5 refutes both the outer-loop
  and the tightened inner-loop convergence statements. No new ID.
- Tyrtyshnikov's rank-increment conjecture: prior source-access hold remains;
  talk slides and abstracts alone do not reconcile generic versus maximum
  rank and field conventions. No new ID.
- Historical one-ninth and LeVeque–Trefethen Kreiss-constant conjectures:
  literature already contains resolutions. No new ID.
