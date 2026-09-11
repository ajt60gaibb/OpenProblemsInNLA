# IE-17 independent proof review

Date: 2026-09-11. **PASS — both monotonicity assertions in the current canonical spectral-norm formulation are false.** Recommend **Resolved (counterexample)** for that unchanged target. No mathematical correction to the submitted proof is required. A source-norm attribution limitation is recorded below. This is an independent Codex mathematical audit, not journal peer review or an exhaustive priority search.

## Complete source and exact target

Read the entire recovered `proofs/IE-17.tex`, including both general lemmas, every numerical certificate, the rational perturbation, the dense variant, and source/scope remarks. Full UTF-8 source normalized only by CRLF-to-LF replacement, with no trimming: **7730 bytes**, SHA256 **`9dece4acf7d067dabb22fb24729fec8d6710c4b1a620b620be5c41e51665b0dc`**. The source is standalone and includes its own preamble; no external TeX input is omitted from this identity.

The provisional recovered IE-17 label matches `linear-systems-and-elimination/IE-17/README.md`. That canonical explicitly asks about matrix-only spectral-norm backward error with b fixed, plus the specified projection approximation, along successive nonzero exact LSMR iterates from zero. It is not a simultaneous perturbation of A and b, a Frobenius-norm substitution, a damped solve, or a floating-point trajectory. The manuscript addresses exactly these displayed definitions.

Locators: Section 1 at line 30; lower-bound Lemma 1 at line 64; completion Lemma 2 at line 76; strict increase at line 97; approximation and rational witness at line 122; source/scope at line 143.

## Iterates and approximation — PASS

For the given integer A and b, A has rank three, H=diag(1,36,25), and g=(11,6,5). The first iterate is a scalar multiple of g. The second is the displayed combination of g and Hg. For each k=1,2, the conditions `(HV_k)^T(g-Hx_k)=0` are exactly the normal equations for minimizing the squared normal-residual norm on the Krylov subspace. Distinct eigenvalues and nonzero components of g make these Krylov columns, and therefore their H images, independent. Thus the supplied x1 and x2 are the unique minimizing iterates. No minimum-length ambiguity occurs. The third Krylov space is all of R^3 and its iterate is (11,1/6,1/5), so both compared iterates are strictly before exact termination and are nonzero.

The residual vectors and their normal-residual squared norms are consistent with direct multiplication. Their decrease is compatible with the backward-error increase and is not used to infer its direction. Since r and x are nonzero at both compared iterates, K has full column rank. The orthogonal projector identity gives `||K K^dagger v||²=v^T K(K^T K)^(-1)K^T v`. Substitution of K, followed by division by ||x||², gives exactly the manuscript's formula for the squared approximation. It uses the same projection quantity as the canonical.

## Lower-bound Lemma 1 — PASS, including zero new residual

For any feasible E with nonzero new residual q=b-(A+E)x, let u=q/||q||. Feasibility gives `(A+E)^T u=0`, hence `||E||_2²>=||E^T u||²=u^T AA^T u`. Orthogonality of q and (A+E)x gives q=uu^T b. Therefore Ex=r-uu^T b, so `||E||_2²>=||r-uu^T b||²/||x||²`. Expanding with b=r+z shows the latter quantity is `u^T D u`: it equals `(||r||²-(u^T r)²+(u^T z)²)/s`. Convex combination and the Rayleigh lower bound prove the claim.

If q=0, the perturbation only immediately yields `||E||_2²>=||r||²/s`. The proof correctly treats this case separately. Because m>n, a unit vector exists in ker(A^T); for it, u^T C u=0 and u^T z=0. Its Rayleigh quotient for tC+(1-t)D is at most ||r||²/s, proving the same eigenvalue lower bound. This avoids excluding perturbations that turn an inconsistent problem into a consistent one. In the example m=4>3, so the hypothesis is satisfied. The lemma does not purport to cover the square case by the same argument.

## Completion Lemma 2 — PASS in spectral norm

The row and column prescriptions have the same scalar intersection: `u^T Ee=e^T E^T u=-u^T Ax/sqrt(s)`. The perpendicular components in the displayed decomposition are correct. Strict upper bounds on both prescribed squared lengths imply d²<kappa, so the completion denominator is nonzero.

In the factorization of E/sqrt(kappa), the middle two-by-two matrix is orthogonal. Each outside rectangular map has norm at most one because the perpendicular component's squared norm is at most kappa-d². Multiplying the factors produces all four blocks of the stated completion, including the coefficient `-d/(kappa-d²)`. Thus its spectral norm is at most sqrt(kappa); no Frobenius-norm estimate is used. The prescriptions give `(A+E)^T u=0` and `(A+E)x=(I-uu^T)b`, which directly imply the perturbed normal equations even if the resulting residual is zero.

For x1, w^T w=63231 and both stated Rayleigh quotients are strictly below 1979/2000. The lemma consequently gives the required first-error upper bound. The alternative rational formula is algebraically the same completion: the normalized perpendicular components are a0/sqrt(omega) and c0/sqrt(s), and d=-h/sqrt(omega s). Substitution removes all square roots and gives the displayed positive h coefficient. Its denominator is positive by d²<kappa.

For x2, the integer matrix K is exactly the stated positive multiple of `(5/6)C+(1/6)D-(99/100)I`. Its four leading principal determinants equal the displayed positive integers. Sylvester's criterion therefore gives a strict lower bound greater than 99/100 for the least eigenvalue of the convex combination. Lemma 1 covers every feasible perturbation, so `mu(x2)²>99/100`, not merely an objective value found by a numerical optimization. Together with the first bound, `mu(x1)²<=1979/2000<99/100<mu(x2)²` follows.

Both exact rational squared-approximation values in Section 4 check out and satisfy the strict rational cutoffs 1.006 and 1.007. Thus the approximation assertion also fails on the same successive iterates. The dense variant uses Q with Q^T Q=4I. Its normal equations are scaled uniformly, leaving Krylov minimizers unchanged. Perturbations correspond bijectively by E'=QE, with spectral norm doubled; the projection formula scales likewise. Consequently both error quantities double and both strict increases persist. The displayed dense A' and b' are correct.

## Independent arithmetic and code inspection

Read the relevant complete implementations in `verification/exact.py` and `verification/checks.py`. Their Fraction arithmetic, Krylov least-squares calculation, primal feasibility checks, leading principal minors, and approximation comparisons correctly implement these finite tests. Function `principal_minors` computes leading principal minors, which is precisely what Sylvester's criterion requires here.

In addition, the reviewer-created standard-library script `verification/reviewer_ie17_19.py` imports no submitted code. It independently verifies the Krylov orthogonality equations, both exact Rayleigh quotients, the rational perturbation's normal equations, positivity of the spectral upper certificate, all four printed lower-certificate determinants, and both huge approximation fractions. It uses permutation-expanded determinants, rather than the submitted elimination implementation. The run passed; output is `verification/reviewer_ie17_19.json`. These exact checks support the arithmetic, while the general completion and universal lower-bound proofs above establish their mathematical force.

## Primary-source comparison and norm caveat

The [Fong–Saunders author paper, Sections 6.1–6.2 and Figure 7.5](https://web.stanford.edu/group/SOL/software/lsmr/LSMR-SISC-2011.pdf) gives the same fixed-b normal-equation perturbation setup and the same approximation, and records the observed LSMR monotonicity. However, its Section 1.1 says the matrix norm usually denotes the Frobenius norm. The unqualified optimal-error notation there must not be relabelled spectral without further source justification. Attempts to retrieve the linked dissertation timed out; this review does not claim that its norm convention was independently verified.

This attribution limitation does not affect the theorem against the current canonical, which explicitly fixes the spectral norm and is disproved by a self-contained spectral completion argument. The report should describe the result as disproving the repository's displayed spectral error and its specified approximation, rather than asserting that every historical norm variant has been refuted. No Frobenius optimal-error monotonicity result is proved here.

**Final scope: PASS for the complete recovered proof and a negative resolution of both current IE-17 claims. No remaining part of that explicit canonical pair is left unanswered.**
