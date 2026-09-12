# RA-04 — Clustered singular-value gaps in randomized block Krylov approximation

**Difficulty:** hard  
**Importance:** interesting to specialist  
**Rating rationale:** Hard because this is a focused spectral-gap refinement of an established Krylov bound; specialist impact reflects the source's assessment that its practical gain is limited.  
**Last checked:** 2026-09-12

**Status:** Partially resolved

## Partial results — 2026-09-12

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation ([verified affiliation](https://www.simonsfoundation.org/people/sidney-holden/)). The [complete report](../../references/holden-ra04-2026-09-12/RA04_partial_results.pdf) and [editable source](../../references/holden-ra04-2026-09-12/src/report.tex) establish the following partial results, with $`m=k'=bt`$ and $`\Delta=\Delta_{k'}^{(b)}`$.

Theorem 5.3 proves all three requested guarantees for every admissible input with

```math
q=O\!\left(\frac{t\log(2m/\Delta)+\log(n/(\delta\varepsilon))}{\sqrt\varepsilon}\right).
```

This has an extra $`t\log m`$ term. The requested iteration order holds when $`\Delta\leq1/m`$ (Corollary 5.4), when the leading spectrum consists of exactly $`t`$ levels each repeated $`b`$ times (Theorem 6.1), when $`t=2`$ with arbitrary admissible leading spectra (Theorem 7.1), and at the endpoints $`b=1`$ and $`b=k`$ (Theorem 6.1 and Corollary 6.2). Proposition 8.1 gives almost-sure exact optimal approximation when $`\mathop{\mathrm{rank}}\nolimits(A)=m`$ after $`t+1`$ blocks. Theorem 4.1 supplies an alternative all-input bound with leading term $`(m-b+1)\log(3/\Delta)`$.

**Remaining target:** the displayed original bound for arbitrary growing $`b,t`$, nonzero-width leading clusters and $`\Delta>1/m`$ is neither proved nor disproved. The report's sufficient interpolation estimate (IE) remains unproved. Its raw-monomial conditioning counterexample (Proposition 9.1) does not refute RA-04, whose algorithm depends on the Krylov subspace.

A [separate independent Codex agent review](../../references/holden-ra04-2026-09-12/verification/independent-review.md) passed the partial arguments and checked the imported convergence theorem against the primary source. This is informal AI-agent review, not external human peer review or formal verification. It does not meet the complete-resolution requirement for **Solved**. [Submission and reproduction record](../../references/holden-ra04-2026-09-12/README.md).

## Original problem (retained)

Let $`A\in\mathbb R^{n\times d}`$ have singular values $`\sigma_1\geq\sigma_2\geq\cdots`$. Fix integers $`1\leq b\leq k`$, set $`t=\lceil k/b\rceil`$, and set $`k'=bt\leq\mathop{\mathrm{rank}}\nolimits(A)`$. Define

```math
\Delta_{k'}^{(b)}=\min_{1\leq i\leq k'-b}
\frac{\sigma_i^2-\sigma_{i+b}^2}{\sigma_i^2},
```

with the empty minimum set to one, and suppose this gap is positive. Draw $`G\in\mathbb R^{n\times b}`$ with independent standard Gaussian entries. In exact arithmetic, let $`Z`$ be an orthonormal basis of

```math
\mathop{\mathrm{range}}\nolimits[G,(AA^T)G,\ldots,(AA^T)^{q-1}G],
\qquad \widehat A=Z[Z^TA]_k,
```

where $`[B]_k`$ denotes a best rank-$`k`$ approximation obtained by truncating the SVD of $`B`$.

Does an absolute constant $`C`$ exist such that, for every such input and every $`0<\varepsilon,\delta<1/2`$, taking

```math
q=\left\lceil C\left[
\frac{t}{\sqrt\varepsilon}\log\frac{2}{\Delta_{k'}^{(b)}}+
\frac1{\sqrt\varepsilon}\log\frac{n}{\delta\varepsilon}
\right]\right\rceil
```

gives, with probability at least $`1-\delta`$, both

```math
\|A-\widehat A\|_\xi\leq(1+\varepsilon)\|A-[A]_k\|_\xi
\quad(\xi=2,F),
```

and $`|\|A v_i\|_2^2-\sigma_i^2|\leq\varepsilon\sigma_{k+1}^2`$ for the ordered top $`k`$ right singular vectors $`v_i`$ of $`\widehat A`$? Here $`\sigma_{k+1}=0`$ if necessary. The factor two makes the logarithm meaningful at a unit gap.

This is the gap-independent algorithmic component of the authors' concluding conjecture. They also conjecture the corresponding improvement in their gap-dependent theorem and random Krylov matrix conditioning theorem; those are not separately counted here. The displayed parameter regime is where the source's spectral-gap expression is finite and defined.

The existing theorem instead depends logarithmically on every consecutive gap and a leading spectral condition number. The proposed bound would explain why a block can accommodate clusters of up to $`b`$ singular values. It does not ask for a finite-precision extension.

## References

1. T. Chen, E. N. Epperly, R. A. Meyer, C. Musco, and A. Rao, *Does block size matter in randomized block Krylov low-rank approximation?*, SODA 2026, pp. 1026–1046 ([published paper](https://doi.org/10.1137/1.9781611978971.42)); arXiv:2508.06486v2. Section 5 states the conjecture; Section 3.3 gives the full quantitative Theorem 1.3, and Algorithm 1 fixes the algorithm. [Paper](https://arxiv.org/html/2508.06486v2).
2. R. A. Meyer, C. Musco, and C. Musco, *On the Unreasonable Effectiveness of Single Vector Krylov Methods for Low-Rank Approximation*, SODA 2024, pp. 811–845, especially Theorem 4.5. [Paper](https://arxiv.org/abs/2305.02535).

## Status check — 2026-09-08

Searched the exact 2025 paper title, “block Krylov b-th order gap conjecture”, and “randomized block Krylov clustered gaps 2026”; checked the current arXiv abstract/version record and Section 5. No proof or counterexample was found. Input perturbation results in Section 3.5 do not establish the unperturbed statement above.

## Audit — 2026-09-10

Rechecked [§5 of the latest arXiv v2](https://arxiv.org/html/2508.06486v2), which retains the clustered-gap conjecture, and added the [SODA 2026 publication](https://doi.org/10.1137/1.9781611978971.42), pp. 1026–1046. Clustered-gap and later low-rank-query searches found no resolution. Randomly perturbing the input changes the displayed target.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
