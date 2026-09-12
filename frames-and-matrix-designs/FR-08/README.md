# FR-08 — Hadamard matrices at every admissible order

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** This longstanding all-order sign-design conjecture underlies optimal real transforms and has broad consequences in combinatorics, coding and experiment design.

Is it true that, for every positive integer $`m`$, there exists a matrix

```math
H\in\{-1,1\}^{4m\times4m}
\quad\text{such that}\quad H^{T}H=4mI_{4m}?
```

Such an $`H`$ is a real Hadamard matrix. The question concerns all admissible orders, rather than a particular currently unconstructed order.

## Relevance
 The normalized matrix $`H/\sqrt{4m}`$ is an orthogonal transform with entries of equal magnitude. Thus this is an existence problem for perfectly conditioned, maximally flat real sign transforms. It differs from Cryer's complete-pivoting growth conjecture already in the collection, which asks about elimination on matrices that already exist.

## References

- A. Bahmanian and S. Suda, *Hadamard Hypercubes*, arXiv:2605.16722 (2026), §1, opening definition and Conjecture 1.1 ([primary manuscript](https://arxiv.org/html/2605.16722v1)).
- A. F. Ramos, D. B. Hulak, and R. J. G. B. de Queiroz, *Multiplier obstructions for Legendre pairs of length 333*, arXiv:2607.20765 (2026), abstract and introduction; a restricted construction problem, not a general obstruction ([primary manuscript](https://arxiv.org/abs/2607.20765)).

## Status check — 2026-09-10
 The May 2026 source states the universal conjecture explicitly. Searches for “Hadamard conjecture”, “proof”, “2026”, and recent construction papers found no general resolution. Individual-order construction announcements do not settle this statement. Because such announcements can rapidly change the smallest unknown order, no particular order is asserted here to remain open. This bounded literature search is not a proof of open status.

**Audit update (2026-09-10):** Rechecked the May 2026 Conjecture 1.1 and searched for later Hadamard constructions and general proofs. Established infinite construction families do not cover every multiple of four; no newly verified general solution was located. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
