# IE-20 — Precision required for conjugate gradients to attain backward accuracy in n steps

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Topic:** Finite-precision Krylov methods.  
**Last checked:** 2026-09-08

This fixes an implementation and arithmetic model for the precision question in the cited workshop report. These conventions are an editorial specialization of its question, not an additional conjecture quoted from the authors.

Let $n\ge1$, $K\ge1$, and $0<\varepsilon<1/2$. At precision $p\ge2$, the inputs are a real symmetric positive definite matrix $A\in\mathbb R^{n\times n}$ and $b\in\mathbb R^n\setminus\{0\}$ whose entries are exactly representable using $p$ binary significant bits and unbounded exponents. They are read exactly, and the error below is measured against these stored inputs. Assume $\kappa_2(A)\le K$.

Use the scalar relative-error model with $u=2^{-p}$:

$$
\operatorname{fl}(a\circ b)=(a\circ b)(1+\delta),
\quad |\delta|\le u,\quad \circ\in\{+,-,\times,/\},
$$

for nonzero divisors, with no underflow or overflow. Guarantees must hold for every choice of permitted operation errors. Products are rounded separately from additions; dot products and matrix-vector rows are accumulated from left to right in index order, starting from zero. Copies, sign changes, and comparisons are exact. The model is an error envelope, not an assumption of independent random roundoff.

Run unpreconditioned conjugate gradients with no restarts, residual replacement, or reorthogonalization. Initialize $x_0=0$, $r_0=p_0=b$, and $\rho_0=\operatorname{fl}(r_0^Tr_0)$. For $j=0,\ldots,n-1$, evaluate

$$
q_j=\operatorname{fl}(Ap_j),\qquad
d_j=\operatorname{fl}(p_j^Tq_j),\qquad
\alpha_j=\operatorname{fl}(\rho_j/d_j),
$$

$$
x_{j+1}=\operatorname{fl}(x_j+\alpha_jp_j),\qquad
r_{j+1}=\operatorname{fl}(r_j-\alpha_jq_j),
$$

and, if another step is needed,

$$
\rho_{j+1}=\operatorname{fl}(r_{j+1}^Tr_{j+1}),\qquad
\beta_j=\operatorname{fl}(\rho_{j+1}/\rho_j),\qquad
p_{j+1}=\operatorname{fl}(r_{j+1}+\beta_jp_j).
$$

Stop when the computed residual vector is zero, or before a division by zero. The performance criterion is that at least one iterate produced before stopping and by step $n$ satisfies

$$
\eta(x_j;A,b):=
\frac{\|b-Ax_j\|_2}{\|A\|_2\|x_j\|_2+\|b\|_2}\le\varepsilon.
$$

Here $b-Ax_j$ is the true residual, not the recursively updated vector $r_j$. Thus early exact convergence succeeds, while a zero computed residual or breakdown does not automatically certify success.

Define $P_{\rm CG}(n,K,\varepsilon)$ as the least integer $p_{\min}\ge2$ such that this criterion holds at every precision $p\ge p_{\min}$, for every admissible stored input at that precision and every permitted rounding-error sequence; set it to infinity if no such threshold exists. Determine, up to universal multiplicative constants, the worst-case dependence of $P_{\rm CG}$ on $n$, $K$, and $\varepsilon$.

The question quantifies the precision cost of the exact-arithmetic finite-termination property for a standard short-recurrence solver.

## References

1. N. Amsel et al., [Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop](https://arxiv.org/html/2602.05394v3), arXiv v3 (2026-08-21), §2.6, Problem 2.17. The question asks for precision sufficient for normwise backward accuracy in at most $n$ CG steps; neighboring Problems 2.15–2.16 emphasize residuals and implementation dependence.
2. C. Musco, C. Musco, and A. Sidford, [Stability of the Lanczos Method for Matrix Function Approximation](https://arxiv.org/abs/1708.07788), SODA 2018, 1605–1624, abstract and discussion of inverse approximation and finite-precision CG. Its polynomial-approximation results are relevant background, not a sharp answer to this target.
3. S. Chenakkod, M. Dereziński, X. Dong, and M. Rudelson, [Well-Conditioned Oblivious Perturbations in Linear Space](https://arxiv.org/abs/2604.23193), 2026, abstract and perturbed-CG application.

## Status check — 2026-09-08

Checked workshop v3, which explicitly retains Problem 2.17 in its August 2026 update. Searches combined “conjugate gradient”, “precision”, “bits”, “n steps”, “backward error”, and 2026. No sharp solution was located. The April 2026 perturbation paper concerns a modified randomized solver and an $O(n)$ matrix-vector bound, not this fixed unperturbed recurrence with an at-most-$n$ requirement. Input rounding is excluded explicitly; other CG implementations and stronger bit-cost claims are outside this model specialization. The bounded literature search is not a proof of current openness.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
