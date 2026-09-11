---
title: "SP-05: A positive-semidefinite minimizing eigenmatrix"
author: "Matthew J. Colbrook"
affiliation: "Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom"
email: "m.colbrook@damtp.cam.ac.uk"
review-footer: "Independent Codex-agent verification; no external human peer review or formal certification."
date: "11 September 2026"
lang: "en-GB"
---

**Status of this manuscript:** Independently checked resolution (Codex-agent review).  
**Outcome:** Affirmative resolution.  
**Prepared:** 11 September 2026.  
**Target:** [Repository entry SP-05](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/SP-05/README.md), snapshot `b412319`.

The original proof draft was generated in a ChatGPT conversation. A separate Codex agent independently checked the complete proof against the exact repository target on 11 September 2026; its [detailed review](../../references/colbrook-2026-09-11/verification/reviews/SP-05-review.md) records **PASS**. The theorem and proof text below are unchanged from the reviewed submission. This verification is an independent agent review, not external human peer review or a formal proof certificate.

## Theorem SP-05: proposed positive-semidefinite minimizer

**Claim.** For any real symmetric positive definite $n\times n$ matrices $A,B$, the operator
$$
\mathcal L(X)=AXB+BXA
$$
has a nonzero real positive-semidefinite eigenmatrix for its smallest eigenvalue. Under column vectorization its matrix is $A\otimes B+B\otimes A$, so this implies the symmetric-minimizer assertion in SP-05.

The Frobenius inner product on complex matrices is $\langle X,Y\rangle=\operatorname{tr}(X^*Y)$. The operator $\mathcal L$ is self-adjoint and positive definite; for example,
$$
\langle X,AXB\rangle=\|A^{1/2}XB^{1/2}\|_F^2>0
\quad(X\ne0).
$$
It also commutes with transposition.

### 1. An inverse that preserves positive semidefiniteness

Put $C=B^{-1/2}AB^{-1/2}\succ0$. In the equation $\mathcal L(X)=Y$, set
$$
\widetilde X=B^{1/2}XB^{1/2},\qquad
\widetilde Y=B^{-1/2}YB^{-1/2}.
$$
Then
$$
C\widetilde X+\widetilde XC=\widetilde Y,
\qquad
\widetilde X=\int_0^\infty e^{-tC}\widetilde Y e^{-tC}\,dt.
$$
The integral converges since $C\succ0$. Differentiating its integrand verifies the equation, and uniqueness follows from positive definiteness of the Sylvester operator. Thus $\Phi=\mathcal L^{-1}$ satisfies
$$
\Phi(Y)=\int_0^\infty M_tYM_t\,dt,
\qquad M_t=B^{-1/2}e^{-tC}B^{-1/2}.
$$
Every $M_t$ is real symmetric. Consequently $\Phi$ maps complex Hermitian positive-semidefinite matrices to positive-semidefinite matrices.

### 2. The top inverse eigenvalue has a real PSD eigenmatrix

Let $r=\lambda_{\max}(\Phi)$. A real eigenmatrix for $r$ exists because $\Phi$ is real self-adjoint. Since $\Phi$ commutes with transposition, at least one nonzero symmetric or skew-symmetric part of that eigenmatrix is also an eigenmatrix for $r$. Call such a part $W$ and define
$$
H=\begin{cases}
W,&W^T=W,\\
iW,&W^T=-W.
\end{cases}
$$
Then $H$ is Hermitian and $\Phi(H)=rH$.

Write $H=H_+-H_-$ with $H_+,H_-\succeq0$, and $|H|=H_++H_-$. Self-adjointness and positivity preservation give
$$
\begin{aligned}
&\langle |H|,\Phi(|H|)\rangle-\langle H,\Phi(H)\rangle\\
&\hspace{1cm}=4\operatorname{tr}\bigl(H_+\Phi(H_-)\bigr)\ge0.
\end{aligned}
$$
The trace is nonnegative because the trace of the product of two Hermitian positive-semidefinite matrices is nonnegative. Also $\||H|\|_F=\|H\|_F$.

In both cases $|H|$ is real symmetric and positive semidefinite. For a real symmetric $W$ this follows by real spectral calculus. For real skew-symmetric $W$,
$$
|H|=\sqrt{H^2}=\sqrt{-W^2},
$$
the real positive-semidefinite square root of the real positive-semidefinite matrix $-W^2$.

The Rayleigh quotient of $|H|$ for $\Phi$ is at least $r$. By the variational characterization of the largest eigenvalue it is also at most $r$, so equality holds and $|H|$ is an eigenmatrix for $r$. It is nonzero because $H\ne0$. Therefore
$$
\mathcal L(|H|)=r^{-1}|H|,
\qquad r^{-1}=\lambda_{\min}(\mathcal L),
$$
which proves the claimed stronger result.

### 3. The displayed symmetric/skew inequality

Let $T\operatorname{vec}(X)=\operatorname{vec}(X^T)$. Then
$$
T(A\otimes B)T=B\otimes A.
$$
For a vector $v$ in either the $+1$ or $-1$ eigenspace of $T$,
$$
v^T(A\otimes B+B\otimes A)v=2v^T(A\otimes B)v.
$$
The two eigenspaces are orthogonal and invariant for the sum. Since its global minimum is attained in the symmetric sector, the minimum Rayleigh quotient of $A\otimes B$ in that sector is at most the minimum in the skew-symmetric sector. This is the precise inequality in the repository entry. $\square$

## Scope and review notes

The proof uses arbitrary real symmetric positive definite A and B, without a commutativity or rank restriction. It concerns the smallest eigenvalue of A tensor B + B tensor A, not a maximum-eigenvalue problem or an indefinite-input generalization.

The independent review checked the congruence reduction for the inverse, use of positivity on the complex Hermitian cone, and the argument that the modulus of iW is real when W is real skew-symmetric. The proof does not assume a simple minimum eigenvalue.

The packaging pass checked the repository statement and contribution rules on 11 September 2026. It did not conduct a new exhaustive literature search or establish novelty.

## Source references

Alex Townsend, *Open Problems in Numerical Linear Algebra* (2026), [entry SP-05](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/SP-05/README.md), repository snapshot `b412319`, accessed 11 September 2026.

N. Kalantarova and L. Tunçel, *On the spectral structure of Jordan–Kronecker products of symmetric and skew-symmetric matrices*, *Linear Algebra and its Applications* 608 (2021), 343–362, [arXiv:1805.09737v3](https://arxiv.org/abs/1805.09737v3), Conjecture 1, equation (7), p. 12. These are the original-source locators recorded by the catalog.
