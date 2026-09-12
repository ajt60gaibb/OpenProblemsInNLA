# RE-01 — Constant-factor HSS approximation in polynomial time

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because shared HSS bases couple approximation choices across levels; community impact is reliable compression for hierarchical numerical solvers.  
**Status:** Open  
**Area:** structured low-rank matrix approximation  
**Last checked:** 2026-09-10  

## Context and notation

Use exact real arithmetic, with comparisons, standard Gaussian sampling, and exact SVDs available as primitives; charge an SVD of an $`a\times b`$ matrix $`O(ab\min(a,b))`$ operations. This states the idealized arithmetic model used here, rather than a finite precision or bit complexity claim. A matrix–vector query returns either $`Av`$ or $`A^\mathsf Tv`$ for one chosen real vector $`v`$; both types count toward the total. Randomized guarantees are for every fixed input, with probability or expectation over the algorithm's randomness.

For $`N=2^{L+1}k`$, $`k,L\ge1`$, form the perfect binary tree that successively halves the ordered index set $`[N]=\{1,\ldots,N\}`$ until every leaf contains $`2k`$ indices. Define $`\mathcal S_{L,k}`$ to contain precisely the real $`N\times N`$ matrices $`B`$ such that, for every nonroot node $`I`$ of this tree,

```math
\mathop{\mathrm{rank}}\nolimits B[I,[N]\setminus I]\le k,
\qquad
\mathop{\mathrm{rank}}\nolimits B[[N]\setminus I,I]\le k.
```

This is the HSS class with rank at most $`k`$, including its constraints across levels. There is no restriction inside a leaf diagonal block. Set

```math
E_{L,k}(A)=\min_{B\in\mathcal S_{L,k}}\|A-B\|_F^2.
```

The minimum exists. The rank definition follows Stefano Massei, Leonardo Robol, and Daniel Kressner, [*hm-toolbox: MATLAB Software for HODLR and HSS Matrices*](https://arxiv.org/pdf/1909.07909v3), SIAM Journal on Scientific Computing **42** (2020), C43–C68, §2.2, Definition 3. Equivalence with the telescoping representation and existence of a minimizer are recorded in Amsel et al., cited below, Definition 3 and Appendix D.

## Problem statement

Do absolute constants $`C,c>0`$ and a uniform randomized algorithm exist that, given the entries of any $`A\in\mathbb R^{N\times N}`$ and integers $`k,L\ge1`$ with $`N=2^{L+1}k`$, returns $`B\in\mathcal S_{L,k}`$ using $`O(N^c)`$ arithmetic operations and satisfies

```math
\mathbb E\|A-B\|_F^2\le C\,E_{L,k}(A)?
```

The exponent and approximation constant must be independent of $`k,L,A`$. A deterministic algorithm is allowed. The output must retain rank at most $`k`$.

## Reference

Noah Amsel, Tyler Chen, Feyza Duman Keles, Diana Halikias, Cameron Musco, Christopher Musco, and David Persson, [*Quasi-optimal Hierarchically Semi-separable Matrix Approximation*](https://arxiv.org/html/2505.16937v2), SIAM Journal on Matrix Analysis and Applications **47** (2026), 586–621, §3.4; Theorems 6 and 12. That section expressly asks for a polynomial-time constant-factor approximation.

## Status evidence

The known squared-error factor is $`O(L)`$. The lower bound near $`2`$ concerns the analyzed greedy algorithm, not all algorithms. Searches for “HSS constant-factor approximation 2026” and “hierarchically semiseparable approximation constant 2026” found no resolution. The latest arXiv version is v2, September 6, 2025; the [journal version](https://doi.org/10.1137/25M176622X) appeared online May 8, 2026.

## Audit — 2026-09-10

Rechecked [Amsel et al., §3.4 and Appendix B.1](https://arxiv.org/html/2505.16937v2) and its [2026 journal record](https://doi.org/10.1137/25M176622X). Constant-factor polynomial-time HSS approximation remains unresolved. Constant-factor and later HSS searches found no solution; the known depth-dependent factor is weaker than this target.
