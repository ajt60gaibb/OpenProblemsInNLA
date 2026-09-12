# SP-06 — A real-valued symbol on a Jordan curve and real Toeplitz spectra

**Topic:** Spectra of finite banded Toeplitz matrices.  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-09-11  

**Rating rationale:** Challenging reflects recovering a spectral implication after a gap in its original analytic proof; community impact is a structural criterion for real spectra of banded Toeplitz sections.

## Resolution — 2026-09-11

**Negative resolution by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](solution.md) · [PDF](solution.pdf) · [LaTeX](solution.tex). **Theorem 1 and equations (1)–(8).**

The integer-coefficient Laurent polynomial in Theorem 1 is real on a rigorously constructed star-shaped Jordan curve enclosing zero, while its $`2\times2`$ Toeplitz section has eigenvalues $`-128\pm8i`$. The proof checks continuity, injectivity and reality on the entire curve. It refutes the conjectured implication for every finite section; it does not refute the distinct limiting-spectrum statement.

The complete argument received an independent Codex-agent **PASS** on 11 September 2026. The [review report](../../references/colbrook-additional-2026-09-11/verification/reviews/SP-06-review.md) records the exact scope and a hash of the original reviewed manuscript. The mathematical sections remain unchanged in the authored version. Original ChatGPT generation is disclosed; no external human peer review or formal proof certificate is asserted. [Submission and verification record](../../references/colbrook-additional-2026-09-11/README.md).

The original statement, source references and prior audit notes are retained; the former difficulty rating is historical.

## Problem statement

Let $`r,s\ge1`$ be integers and

```math
b(z)=\sum_{k=-r}^{s}b_kz^k,
\qquad b_k\in\mathbb C,\qquad b_{-r}b_s\ne0.
```

For every $`n\ge1`$, define $`T_n(b)=(b_{i-j})_{i,j=1}^n`$, with $`b_k=0`$ outside $`[-r,s]`$. Suppose there is a Jordan curve $`\gamma\subset\mathbb C\setminus\{0\}`$ such that $`b(z)\in\mathbb R`$ for every $`z\in\gamma`$. A Jordan curve means the image of a continuous injective map from the unit circle.

Must

```math
\mathop{\mathrm{spec}}\nolimits(T_n(b))\subset\mathbb R
\qquad\text{for every integer }n\ge1?
```

## Why it matters

The conjecture would characterize a broad source of real spectra in nonsymmetric structured eigenvalue problems through a scalar symbol condition, uniformly over matrix size.

## References

- B. Shapiro and F. Štampach, [Non-Self-Adjoint Toeplitz Matrices Whose Principal Submatrices Have Real Spectrum](https://arxiv.org/abs/1702.00741), *Constructive Approximation* 49 (2019), 191–226. Equation (2), Theorem 1(ii)–(iii), and Theorem 8; use arXiv v4, which includes the correction.
- B. Shapiro and F. Štampach, [Correction to the same article](https://doi.org/10.1007/s00365-022-09614-0), 2023. The correction, pp. 27–28 of the combined arXiv PDF, withdraws the proof of (ii)$`\Rightarrow`$(iii) and explicitly proposes the implication as conjectural.
- D. Giandinoto, [On reality of eigenvalues of banded block Toeplitz matrices](https://arxiv.org/abs/2411.16266), 2024, introduction and §2. The paper describes the corrected scalar implication as a conjecture before considering a block generalization.

## Earlier status check — 2026-09-08

On 2026-09-08, checked the corrected arXiv v4 (2022-12-29), its appended erratum, and Giandinoto's November 2024 paper. Searches combined “Shapiro”, “Štampach”, “Toeplitz”, “reality”, “erratum”, “Jordan curve”, “proof”, and 2026. No general resolution was located. The original article's theorem label is misleading without its correction: the finite-spectrum implication above remains the authors' stronger proposed statement. Its weaker limiting-spectrum consequence and particular symbol families are not separate catalog problems here.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

## Audit update — 2026-09-10

Rechecked the appended erratum in [Shapiro–Štampach, version 4](https://arxiv.org/pdf/1702.00741), printed p. 27. It withdraws the relevant implication's proof and retains it as a conjecture, so the original theorem wording must not be treated as a solution. Jordan-curve/Toeplitz searches and [Giandinoto's later work](https://arxiv.org/abs/2411.16266) did not identify a proof of this scalar sufficiency implication.
