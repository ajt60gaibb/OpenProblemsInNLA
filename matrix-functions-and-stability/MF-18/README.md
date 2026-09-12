# MF-18 — Imaginary-part rank in a limiting Green-function matrix equation

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Last checked:** 2026-09-11  
**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Historical: challenging because the limiting complex solution must be tied exactly to unit-circle eigenstructure; specialist impact is on structured Green-function matrix equations.

**Status:** Solved

<!-- stepaniants-mf18-resolution -->
## Resolution - 2026-09-11

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

**Solved affirmatively.** [Theorem 1 and Sections 1-4 of the complete proof](solution.md) establish the displayed rank equality for the full complex $C,D,R,P$ model. The proof includes singular $C$ or $D$, simple unit-circle roots at $1$ or $-1$, $m=0$, and arbitrary Jordan structure strictly inside the disk. The finite nonsingular limit and simple unit-circle eigenvalues remain assumptions, exactly as in the original target.

[Proof PDF](solution.pdf) · [Standalone TeX](solution.tex) · [Independent mathematical review](../../references/stepaniants-mf18-2026-09-11/verification/MF-18-independent-review.md) · [Authorship, source history and public-branch audit](../../references/stepaniants-mf18-2026-09-11/README.md).

The proof passed a separate Codex-agent review against the exact canonical statement and the original paper. It was developed with substantial ChatGPT/Codex assistance; this verification is independent automated-agent review, not external human peer review or formal certification. On 11 September 2026, the pre-submission audit found only the earlier partial result across five public repositories and all 29 public branch heads. The original target, permanent ID and canonical path are retained. Difficulty and importance above are historical ratings.
<!-- /stepaniants-mf18-resolution -->

<!-- colbrook-matrix-functions -->
## Earlier auxiliary result; original scope retained — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the stated real-coefficient auxiliary theorem.**

For real $A,Q$ with $Q=Q^\top$, scalar regularization $i\eta I$, and a finite invertible stabilizing limit, the manuscript proves that the imaginary-part rank is half the number of odd unit-circle Jordan blocks. It also establishes semisimple regularity and an exact defective example.

This auxiliary result did not settle the canonical general complex $C,D,R,P$ problem. Its simple-eigenvalue real subcase was already known; the defective extension is a distinct auxiliary result outside the canonical simple-eigenvalue hypothesis. The general complex target is now settled by the resolution above. This earlier contribution and its independent review retain their original attribution and scope.

**Primary reference:** [complete authored PDF](../../references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-18.pdf), [standalone TeX](../../references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-18.tex), **Theorem 1 and Corollary 3; Section 8 exact defective example**. [Independent proof review](../../references/colbrook-matrix-functions-2026-09-11/verification/reviews/MF-18-review.md) · [Authorship and submission record](../../references/colbrook-matrix-functions-2026-09-11/README.md). Verification is independent agent review, not external human peer review or formal certification.

<!-- /colbrook-matrix-functions -->

## Problem statement

Let $n\geq1$, let $C,D,R,P\in\mathbb C^{n\times n}$, and write $M^*$ for conjugate transpose. Suppose $R=R^*$, $P=P^*$, and

$$
P+\lambda D^*+\lambda^{-1}D\succ0
\qquad (|\lambda|=1).
$$

For each $\eta>0$, let $X_\eta$ be the unique nonsingular solution of

$$
X_\eta+(C^*+i\eta D^*)X_\eta^{-1}(C+i\eta D)
 =R+i\eta P
$$

satisfying $\rho(X_\eta^{-1}(C+i\eta D))<1$, where $\rho$ denotes spectral radius. Assume the finite limit $X_0=\lim_{\eta\downarrow0}X_\eta$ exists and is nonsingular. Assume the matrix polynomial

$$
\mathcal P_0(\lambda)=\lambda^2C^*-\lambda R+C
$$

is regular, meaning $\det\mathcal P_0(\lambda)\not\equiv0$. Suppose its eigenvalues on the unit circle are all simple (algebraic multiplicity one). Their number is even; denote it by $2m$.

Is it always true that

$$
\operatorname{rank}\!\left(\frac{X_0-X_0^*}{2i}\right)=m?
$$

## Why this matters for NLA

The rank describes the non-Hermitian part of the selected matrix-equation solution in Green-function computations. It connects a limiting nonlinear solve to the spectrum of a structured quadratic polynomial.

The source proves the upper bound by $m$. Its earlier SIAM paper proves equality for real $C,R$, $P=I$, $D=0$; the resolution above establishes the general complex equality. Existence of the limit remains an assumption.

## References

1. C.-H. Guo, Y.-C. Kuo, W.-W. Lin, [*Numerical solution of nonlinear matrix equations arising from Green's function calculations in nano research*](https://doi.org/10.1016/j.cam.2012.05.012), JCAM 236 (2012), 4166–4180: equation (1), Theorems 3 and 5, and the conjecture on p. 4172. [Author manuscript](https://uregina.ca/~chguo/JCAM_GuoKuoLin.pdf): pp. 1, 5–8.
2. The same authors, [*On a nonlinear matrix equation arising in nano research*](https://doi.org/10.1137/100814706), SIMAX 33 (2012), 235–262, §3: the real-coefficient case.

## Status check

On 2026-09-08, checked both papers' scope and Guo's [publication list through 2026](https://uregina.ca/~chguo/paper.html). Searches using the JCAM title, authors, “Green rank conjecture,” “weakly stabilizing,” and 2025/2026 found no general resolution. The source proves only the upper bound in the stated complex setting. This is a bounded literature check.

## Audit — 2026-09-10

Rechecked [Guo–Kuo–Lin, Theorem 5 and its following conjecture](https://uregina.ca/~chguo/JCAM_GuoKuoLin.pdf). The general complex equality remains posed, while the cited earlier real-coefficient case is settled. Exact-title, author, and rank-conjecture searches found no general resolution. The upper bound alone does not prove equality.
