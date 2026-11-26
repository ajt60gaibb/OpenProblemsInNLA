# AC-13 — Deterministic near-quadratic matrix multiplication verification

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Partially resolved  
**Last checked:** 2026-11-26

**Rating rationale:** Matching randomized verification in deterministic near-quadratic bit time is a longstanding derandomization barrier, with obstructions known for restricted algorithm classes. Exact matrix verification has broad importance across linear algebra and computational complexity.

**Area:** computational complexity; exact linear algebra  

## Problem statement

For every fixed constant $`c>0`$, is there a deterministic algorithm that, given three explicitly represented $`n\times n`$ matrices $`A,B,C`$, decides exactly whether

```math
AB=C
```

in $`\widetilde O(n^2)`$ bit operations in each of the following input domains?

1. Integer matrices with every input entry in $`[-n^c,n^c]`$.
2. Matrices over a finite field $`\mathbb F_q`$ with $`q\le n^c`$.

Here $`\widetilde O(n^2)`$ means $`O(n^2(\log n)^d)`$ for a constant $`d`$ independent of the matrices and $`n`$; constants may depend on $`c`$. Integers use binary encoding. For the finite-field case, use a standard explicit field representation: $`q=p^r`$, elements represented by polynomials of degree less than $`r`$ over $`\mathbb F_p`$, and an irreducible degree-$`r`$ modulus supplied with the input. The field representation is promised valid. Arithmetic and intermediate bit lengths contribute to the running time.

The answer must be correct on every input. There is no sparsity, rank, symmetry, or nonsingularity promise, and no auxiliary certificate from a prover. This is one derandomization question across the two domains explicitly identified in the source. The field-encoding convention makes its bit-cost interpretation explicit.

Verification is a basic task for checking exact matrix computations. Freivalds's randomized test already has near-quadratic bit complexity for these domains. Counting operations on arbitrarily large integers at unit cost would change the question.

## References

Huck Bennett, Karthik Gajulapalli, Alexander Golovnev, and Evelyn Warton, [*Matrix Multiplication Verification Using Coding Theory*](https://arxiv.org/pdf/2309.16176v2), RANDOM 2024, [LIPIcs 317, Article 42](https://doi.org/10.4230/LIPIcs.APPROX/RANDOM.2024.42); full version §1.3, p. 10, and Definition 2.6, p. 12. Section 1.2 discusses why an existing quadratic arithmetic-operation algorithm is not a quadratic bit algorithm.

The same authors, [*Output-Sparse Matrix Multiplication Using Compressed Sensing*](https://arxiv.org/pdf/2508.10250), 2025 preprint, accepted at RANDOM 2026; §1.1, Theorems 1–2, and §1.2 explain the later sparse-product advances and their relationship to verification.

## Status check — 2026-09-10

Checked Bennett–Gajulapalli–Golovnev–Warton v2, §§1.1–1.3, the 2025 follow-up, and targeted deterministic-verification/2025–2026 searches. The 2024 paper recounts a deterministic near-quadratic algorithm under the promise that $`AB-C`$ has at most $`n`$ nonzero entries, a substantive solved input subclass. Its newer coding-theory and sparse-product results do not yield the required unrestricted near-quadratic bit bound. No such general algorithm was located. The paper’s lower-bound barrier concerns a restricted class of linear-algebraic algorithms; it is not an unconditional impossibility theorem. Unbounded unit-cost integer arithmetic changes the target model.

## Literature update — 2026-11-26

Xiangle Chen's November preprint, Theorem 1 and Corollary 2, reports that
deterministic verification on arbitrary real inputs has the same
arithmetic exponent as matrix multiplication. The theorem bounds the
border rank of a bilinear map by a constant times the cost of a real
decision tree that verifies its output. Applied with [AC-01](../AC-01/README.md),
this yields the reported $`\Omega(n^{9/4})`$ real decision-tree lower bound.
The real model charges unit cost for exact arithmetic and comparisons,
and correctness ranges over all real matrices. The bounded-integer and
finite-field bit-complexity questions above remain open.
[Preprint, Theorem 1 and Corollary 2](https://arxiv.org/html/2611.34814v1).
