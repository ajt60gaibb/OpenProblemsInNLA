# AV-03 — Polynomial-time solution under the regularity promise

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Open  
**Area:** algorithms for piecewise linear systems and complementarity  
**Last checked:** 2026-09-10  

**Rating rationale:** Extreme reflects the longstanding polynomial-time barrier for P-matrix complementarity in an equivalent regular AVE form; broad impact spans optimization, complexity, and piecewise linear systems.

## Context and notation

Absolute values and vector inequalities are componentwise. All algorithmic questions use rational input in binary and the deterministic Turing model. Input length includes the matrix dimensions and the bit lengths of all rational coefficients.

For a real square matrix $`A`$, define the diagonal perturbation family

```math
\mathcal D(A)=\{A-\mathop{\mathrm{diag}}\nolimits(d):d\in[-1,1]^n\}.
```

Call this family **regular** when every member is nonsingular. Only diagonal entries vary. This is precisely the entrywise interval matrix $`[A-I_n,A+I_n]`$.

## Problem statement

Is there a deterministic algorithm and a polynomial $`p`$ such that, for every $`n\ge1`$, rational $`A\in\mathbb Q^{n\times n}`$ and $`b\in\mathbb Q^n`$ with regular $`\mathcal D(A)`$, the algorithm outputs the exact rational vector $`x`$ satisfying

```math
Ax-|x|=b
```

within $`p(\ell)`$ bit operations, where $`\ell`$ is the binary input length?

The promise guarantees existence and uniqueness. No certificate of regularity is supplied or required, and behavior on inputs violating the promise is unrestricted. Polynomial dependence on coefficient bit length is allowed; this does not ask for a strongly polynomial algorithm.

## References

Milan Hladík, Hossein Moosaei, Fakhrodin Hashemi, Saeed Ketabchi, and Panos M. Pardalos, [*An overview of absolute value equations: from theory to solution methods and challenges*](https://doi.org/10.1007/s10589-025-00717-5), Computational Optimization and Applications **93** (2026), 435–488, §2.4.2, paragraph following conditions (15)–(16); §2.2 gives the complementarity connection.

This is the AVE formulation of the polynomial-time P-matrix linear complementarity problem; it is counted once. Michaela Borzechowski, John Fearnley, Spencer Gordon, Rahul Savani, Patrick Schnider, and Simon Weber, [*Two Choices Are Enough for P-LCPs, USOs, and Colorful Tangents*](https://doi.org/10.4230/LIPIcs.ICALP.2024.32), ICALP 2024, §1, explicitly retain that algorithmic question.

## Earlier status evidence — 2026-09-08

The survey appeared online August 8, 2025. Borzechowski et al.'s latest [arXiv version](https://arxiv.org/abs/2402.07683) is v2, May 21, 2024. Searches for “P-matrix linear complementarity 2026 polynomial-time” and “P-LCP solved polynomial algorithm” found no solution. E.-Nagy and Végh's [June 30, 2026 revision](https://arxiv.org/html/2605.10701v2), abstract and §6, gives an algorithm whose complexity also depends on an optimized handicap number; it does not give the required polynomial bound in input length alone.

## Audit update — 2026-09-10

Rechecked the [2025 survey](https://link.springer.com/article/10.1007/s10589-025-00717-5), §2.4.2, and [E.-Nagy–Végh's 2026 handicap reduction](https://arxiv.org/html/2605.10701v2). The latter's complexity also depends on its handicap parameter, so it does not establish a bound polynomial solely in the displayed input length. P-LCP/regular-AVE polynomial-time searches found no such algorithm or matching resolution.
