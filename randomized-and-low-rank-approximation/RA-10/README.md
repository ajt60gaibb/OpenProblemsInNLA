# RA-10 — Constant-loss nuclear-error transfer without matrix ordering

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Historical assessment of the original question: challenging because a dimension-independent loss must survive removal of matrix ordering; community impact is transferring nuclear-error guarantees between matrix functions.  
**Topic:** Low-rank approximation of matrix functions.  
**Last checked:** 2026-09-11  
**Status:** Solved  

<!-- stepaniants-ra10-resolution -->
## Resolution - 2026-09-11

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

**Affirmative resolution: the universal constant $`C=11`$ works.** [Theorem 1 of the complete proof](solution.md) covers every matrix size, allowed rank, real PSD pair, nonnegative continuous operator-monotone function and $`\varepsilon\ge0`$ in the original statement. It retains every permitted choice of ordered eigenvectors, including ties, selected zero eigenvalues, $`f(0)>0`$ and zero optimal tail. No ordering or commutation assumption is added. No case of the canonical nuclear-norm question remains open; optimality of 11 and other norms are not claimed.

[Proof PDF](solution.pdf) · [Standalone TeX](solution.tex) · [Independent Codex-agent review: PASS](../../references/stepaniants-ra10-2026-09-11/verification/RA-10-independent-review.md) · [Authorship, source identities and submission record](../../references/stepaniants-ra10-2026-09-11/README.md).

The new estimate is the compression bound in **Lemma 2**; Sections 3-5 give the spectral replacement, constant 11 and positive-integral reductions. The work used substantial ChatGPT/Codex assistance. The separate agent review and coordinating-agent source audit are documented; external human peer review and formal certification are not asserted. The original statement, ID and historical ratings are retained below.
<!-- /stepaniants-ra10-resolution -->

<!-- colbrook-transfer -->
## Earlier partial result - 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the limited result below.**

The sharp nuclear relative-excess factor is two when $`A`$, $`B=\widehat A_k`$ and the actual selected rank-$`k`$ projector have a simultaneous orthonormal eigenbasis. The finite-Schatten extension is also proved. Diagonal operator-monotone power examples show that any constant solving the full question must satisfy $`C\ge2`$.

**Historical scope:** At the time of this partial result, existence of a finite universal constant for arbitrary noncommuting PSD pairs remained open. The full nuclear-norm question is answered above with $`C=11`$. Commutation of $`A`$ and $`\widehat A`$ alone does not cover every truncation inside a repeated eigenspace. The separate scalar-concave nuclear counterexamples use functions outside the required operator-monotone class.

**Primary reference:** [complete authored PDF](../../references/colbrook-transfer-2026-09-11/manuscripts/06_commuting_schatten_transfer.pdf), [standalone TeX](../../references/colbrook-transfer-2026-09-11/manuscripts/06_commuting_schatten_transfer.tex), **Theorem 1.1 and Section 3**. [Independent proof review](../../references/colbrook-transfer-2026-09-11/verification/reviews/RA-10-review.md) · [Authorship and submission record](../../references/colbrook-transfer-2026-09-11/README.md). Verification is independent agent review, not external human peer review or formal certification.

<!-- /colbrook-transfer -->

Does a universal constant $`C\ge1`$ exist with the following property? For every $`n\ge2`$, $`1\le k< n`$, real symmetric positive semidefinite matrices $`A,\widehat A\in\mathbb R^{n\times n}`$, $`\varepsilon\ge0`$, and continuous operator-monotone function $`f:[0,\infty)\to[0,\infty)`$,

```math
\|A-\widehat A_k\|_*\le(1+\varepsilon)\|A-A_k\|_*
```

implies

```math
\|f(A)-f(\widehat A)_k\|_*\le(1+C\varepsilon)\|f(A)-f(A)_k\|_*?
```

Here $`\|M\|_*=\sum_i\sigma_i(M)`$ is the nuclear norm. Operator monotonicity means $`f(H)\succeq f(G)`$ for every size and every real symmetric $`H\succeq G\succeq0`$; functions of matrices are defined spectrally. No ordering between $`A`$ and $`\widehat A`$ is assumed.

For an ordered orthonormal eigendecomposition $`X=\sum_{i=1}^n\lambda_iq_iq_i^T`$ of a PSD matrix, set

```math
X_k=\sum_{i=1}^k\lambda_iq_iq_i^T,
\qquad f(X)_k=\sum_{i=1}^kf(\lambda_i)q_iq_i^T.
```

The assertion must hold for every choice of ordered eigenvectors, using the same choice in both truncations. $`C`$ must be independent of all inputs, including $`f`$.

This is the nuclear-norm instance of the authors' explicit question about a fixed loss in approximation accuracy. It asks whether the ordering condition in existing transfer results can be removed at a controlled price.

## References

1. D. Persson, R. A. Meyer, and C. Musco, [Algorithm-agnostic low-rank approximation of operator monotone matrix functions](https://arxiv.org/html/2311.14023v2), *SIAM Journal on Matrix Analysis and Applications* 46 (2025), 1–21. §1.2, paragraph immediately preceding Table 1; §5, Example 5.3 and closing paragraph; Theorem 2.4 is the ordered predecessor. Equation (2) specifies truncation.
2. D. Persson, T. Chen, and C. Musco, [Randomized block-Krylov subspace methods for low-rank approximation of matrix functions](https://arxiv.org/abs/2502.01888), *Linear Algebra and its Applications* 741 (2026), 32–65, abstract and algorithmic scope.

## Historical status check - 2026-09-08

Checked the source's latest listed arXiv v2 (2024-07-04), its 2025 journal record, and the exact counterexample and constant-loss discussion. Searches combining the title, “constant”, “counterexamples”, “nuclear”, “funNyström”, and 2026 found no general resolution. Example 5.3 rules out $`C=1`$, while the source expressly leaves a larger fixed constant possible. The 2026 Krylov work addresses specific algorithms, not arbitrary PSD approximation pairs. This entry is explicitly a specialization of the source's broader question; the source does not number it as a separate conjecture. No later explicit reaffirmation was located.

## Historical audit - 2026-09-10

Rechecked [Theorem 2.4 and Example 5.3](https://arxiv.org/html/2311.14023v2): ordered pairs satisfy $`C=1`$, while unordered pairs can violate that constant. At that audit, a larger universal constant remained open. Constant-loss nuclear-transfer searches found no resolution; the partial tag refers only to the ordered subclass.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
