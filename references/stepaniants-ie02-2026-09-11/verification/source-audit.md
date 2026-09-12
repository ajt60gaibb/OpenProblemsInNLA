# IE-02 source and scope audit — 11 September 2026

This is an author source check, not an independent review of RESULT.md.

The canonical target was read from
`/tmp/nla-mf22-worktree/linear-systems-and-elimination/IE-02/README.md`.
It requires the complex-vector, complex-polynomial equality for every
nonzero complex eigenvalue, every dimension n at least 2, and every
1 <= k < n. No target text was changed.

Primary sources inspected:

- Tichý–Liesen–Faber (ETNA26, 2007), author PDF
  <https://www.karlin.mff.cuni.cz/~ptichy/download/public/TiLiFa2007.pdf>.
  Read the conjecture, §§2–5, including Theorem3.2, Theorem4.2,
  Corollary4.4, Theorem5.5, and Corollary5.6. These establish special
  cases but not the full target. The old manuscript also mentions the
  relation between polynomial numerical hulls and CF interpolation;
  merely mentioning CF therefore is not new. The simultaneous
  preservation lemma is the substantive additional step here.
- Faber–Liesen–Tichý, *Matrix best approximation in the spectral norm*,
  arXiv:2506.09687, published LAA733(2026),
  <https://arxiv.org/html/2506.09687>. Read the Jordan-block Example15
  and §§4–5. Example15 concerns a monic Arnoldi approximation; it is
  not the normalized GMRES question. The convex optimality and
  minimax criteria are consistent with Lemma5 and Theorem6 of our
  argument. The source's doubling result is not used.
- Courtney–Sarason, *A mini-max problem for self-adjoint Toeplitz
  matrices*, Math.Scand.110(2012),82–98,
  <https://www.mscand.dk/article/download/15198/13193/34699>.
  Despite the title, TheoremCF on printed p.84 explicitly concerns
  lower triangular Toeplitz matrices. Read its definition of the
  inducing-function class on p.82 and TheoremCF on p.84. The result
  supplies a norm-preserving finite Blaschke inducing function with
  order at most n−1 for an n-by-n triangular matrix. Its analytic
  coefficients are the matrix's first column. This is exactly the
  finite compression used in Lemma2. TheoremCF's uniqueness is not
  needed in our proof.

Searches included combinations of Jordan block, triangular Toeplitz,
ideal GMRES, worst-case GMRES, Carathéodory–Fejér, Fejér–Riesz,
Blaschke, and spectral factorization. No later full solution was found
in this bounded search. This is not an assertion of exhaustive novelty.

`coefficient_diagnostic.py` and its JSON are numerical discovery records,
not certificates. They include negative coefficients and nearly repeated
maximal singular values, which suggested that a coefficient-positivity
or simple-singular-value shortcut would be inadequate. No value in them
is used in RESULT.md.

The complete proposed proof is independent of numerical computation. Its
only external analytic theorem is the cited finite CF theorem; the scalar
Fejér–Riesz fact is reproved by polynomial roots. The finite-dimensional
optimality statement is also proved, including complex tangents. The
stronger affine Toeplitz conclusion explains why no restriction on the
complex eigenvalue or the degree/dimension arithmetic is needed.
