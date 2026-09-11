# IE-27 — Spectral disk for a Radau stage preconditioner

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Preconditioning and eigenvalue localization  
**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** The conjecture requires a sharp enclosure for a nonnormal matrix family at every Runge–Kutta order and positive shift. It would explain mesh- and time-step-independent spectral clustering of a practical preconditioner.

## Statement

Let $q\ge2$, and let $A_q\in\mathbb R^{q\times q}$ be the Butcher matrix of the $q$-stage Radau IIA method. Explicitly, if $0<c_1<\cdots<c_q=1$ are the roots in $[0,1]$ of $P_q(2t-1)-P_{q-1}(2t-1)$, where $P_j$ is the degree-$j$ Legendre polynomial normalized by $P_j(1)=1$, and $\ell_j$ are their Lagrange cardinal polynomials, then

$$ (A_q)_{ij}=\int_0^{c_i}\ell_j(t)\,dt.$$

Take the exact factorization $A_q^{-1}=L_qU_q$ without pivoting, with $L_q$ lower triangular and $U_q$ upper triangular with unit diagonal. Write $\widehat U_q=U_q-I_q$, and assume $\|\widehat U_q\|_2<1$.

For $n\ge1$, let $M,K\in\mathbb R^{n\times n}$ be symmetric positive definite mass and stiffness matrices from a finite-element discretization of a coercive self-adjoint second-order elliptic operator, and let $\tau>0$. Define

$$\mathcal A=A_q^{-1}\otimes M+\tau I_q\otimes K,
\qquad\mathcal P_L=L_q\otimes M+\tau I_q\otimes K.$$

**Conjecture.** Every generalized eigenvalue $\nu\in\mathbb C$ of $\mathcal Ax=\nu\mathcal P_Lx$ satisfies

$$|\nu-1|\le\|\widehat U_q\|_2.$$

The quantifiers are uniform over the stage number, admissible spatial discretization and positive time step. This states the symmetric elliptic setting used by the later spectral analysis explicitly. The original Conjecture 1 says “positive definite” finite-element matrices, and also discusses convection; this page does not silently identify nonsymmetric positive definiteness with the symmetric setting.

## Equivalent small matrices and known cases

The Kronecker structure reduces the spectrum to matrices

$$X_{q,\mu}=I_q+(I_q+\mu L_q^{-1})^{-1}\widehat U_q,
\qquad \mu\in\sigma(\tau M^{-1}K)\subset(0,\infty).$$

In particular, proving $\rho(X_{q,\mu}-I_q)\le\|\widehat U_q\|_2$ for every $\mu>0$ proves the displayed conjecture for all admissible discretizations. The source proves the two-stage case. At least $n$ eigenvalues equal one because $\widehat U_q\otimes I_n$ has nullity at least $n$; this established part of the original conjecture is not an additional target. Numerical spectra at larger stage counts support the enclosure, but do not settle all $q$ and $\mu$.

## References and status check

- O. Axelsson, I. Dravins and M. Neytcheva, *Stage-parallel preconditioners for implicit Runge–Kutta methods of arbitrarily high order, linear problems*, Numerical Linear Algebra with Applications 31(1) (2024), e2532; first published 19 September 2023. [DOI and full text](https://doi.org/10.1002/nla.2532); [institutional PDF](https://www.diva-portal.org/smash/get/diva2%3A1740890/FULLTEXT01.pdf). §5.2, Conjecture 1, equations (17)–(18), and Theorem 1.
- M. Outrata, *On recent advances of spectral analysis for systems arising from fully-implicit RK methods*, Proceedings in Applied Mathematics and Mechanics (2026), e70082. [DOI](https://doi.org/10.1002/pamm.70082); [author preprint arXiv:2510.21241v1](https://arxiv.org/html/2510.21241v1). §2.1, after equation (7), recalls the open general-stage conjecture; §2.3, equation (23), gives the small-matrix equivalence. The preprint says “diameter” at that point, whereas the original conjecture unambiguously specifies **radius**; the display follows the original.

On 2026-09-11, checked the original published conjecture and its two-stage theorem, Outrata's 2025 preprint and 2026 publication record, and searches for the title, Radau spectral-disk conjecture, stage-parallel preconditioner proofs and counterexamples. No proof or counterexample for arbitrary stage count was located. Later symbolic spectral reductions are not a general proof of this particular disk radius. The check is bounded. This is distinct from the [diagonal nilpotent-preconditioner existence question](../IE-28/README.md) and from the repository's Krylov convergence and elimination-growth targets.
