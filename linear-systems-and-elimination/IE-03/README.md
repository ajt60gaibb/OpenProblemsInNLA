# IE-03 — Cryer's Hadamard complete-pivoting conjecture

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-10  

**Rating rationale:** Extreme reflects a longstanding conjecture across every Hadamard order and pivot path; community impact comes from sharp complete-pivoting stability and its connection to Hadamard structure.

## Context and notation

All elimination in this problem is in exact arithmetic. Write $`\|A\|_{\max}=\max_{ij}|a_{ij}|`$. A pivoting path creates successive active Schur complements $`S_1=A,S_2,\ldots,S_n`$, with row/column permutations as appropriate. Its element-growth factor is

```math
\rho(A)=\frac{\max_{1\leq j\leq n}\|S_j\|_{\max}}{\|A\|_{\max}}.
```

Partial pivoting chooses a largest-magnitude entry in the active first column; complete pivoting chooses one anywhere in the active matrix. If ties occur, a universal statement includes every admissible tie choice; a supremum includes all admissible paths. These conventions remove implementation-dependent ambiguity. Matrices are nonsingular unless otherwise stated.

## Problem statement

A real Hadamard matrix of order $`n`$ is a matrix $`H\in\{-1,1\}^{n\times n}`$ satisfying $`HH^T=nI`$. Prove or disprove that, for every Hadamard matrix and every complete-pivoting path,

```math
\rho(H)=n.
```

The quantified input is an existing Hadamard matrix; this question does not ask whether Hadamard matrices exist in every order divisible by four. Since $`\|H\|_{\max}=1`$, the requested upper bound says that no entry in any active Schur complement can exceed $`n`$ in absolute value. The final pivot already supplies the matching lower bound. Permuting or resigning rows and columns does not remove the need to account for all allowed pivot paths.

## References

N. J. Higham, [*Accuracy and Stability of Numerical Algorithms*,
2nd ed.](https://doi.org/10.1137/1.9780898718027), SIAM (2002), Problem 9.17,
p. 193, poses this book-sourced question. Kravvaritis and Mitrouli, [*The growth factor of a Hadamard matrix of order 16 is 16*](https://doi.org/10.1002/nla.637), NLA with Applications 16 (2009), 715–743, introduction and main result. Peca-Medlin, [*Complete pivoting growth of butterfly matrices and butterfly Hadamard matrices*](https://doi.org/10.1080/03081087.2026.2660796), 2026, introduction and §2.

## Earlier status check — 2026-09-08

Searches for `Hadamard Cryer 2026` and `Hadamard growth conjecture 2026 proof` found the general conjecture still identified as open in the 2026 butterfly paper. Shah–Urschel's August 2026 general elimination construction is not a Hadamard counterexample. Known Sylvester and small-order cases must not be counted as additional open problems.

## Audit update — 2026-09-10

The [2026 butterfly paper](https://www.tandfonline.com/doi/abs/10.1080/03081087.2026.2660796), §3, retains the general Hadamard conjecture while recording proofs for Sylvester-type matrices in all their orders and every Hadamard matrix of order at most 16. Hence the status now records partial resolution. Searches for Cryer/Hadamard growth and later complete-pivoting results found no general proof or counterexample; asymptotic bounds for unrestricted matrices do not settle this subclass.
