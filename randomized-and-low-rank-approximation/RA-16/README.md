# RA-16 — Super-exponential decay of the zero-permanent probability

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme
**Importance:** interesting to the community
**Rating rationale:** Extreme difficulty reflects the unresolved passage from a fixed exponential rate to arbitrarily large rates, despite the recent exponential breakthrough. The question concerns a central cancellation phenomenon in combinatorial random-matrix theory, supporting community importance.
**Status:** Open
**Last checked:** 2026-09-10

## Problem statement

For each integer $`n\ge1`$, let $`A_n=(a_{ij})\in\mathbb R^{n\times n}`$ have independent entries with
$`\Pr(a_{ij}=1)=\Pr(a_{ij}=-1)=1/2`$. Define

```math
\mathop{\mathrm{per}}\nolimits A_n=\sum_{\sigma\in S_n}\prod_{i=1}^n a_{i,\sigma(i)}.
```

Is it true that, for every real $`c>0`$, there exists $`N_c`$ such that

```math
\Pr(\mathop{\mathrm{per}}\nolimits A_n=0)\le e^{-cn}\qquad\text{for every }n\ge N_c?
```

Equivalently, $`\lim_{n\to\infty}\Pr(\mathop{\mathrm{per}}\nolimits A_n=0)^{1/n}=0`$.
This explicitly quantifies the source's phrase “super exponentially small.”

## Relevance and ratings

The question concerns cancellation in a multilinear function of a random matrix. It complements random-matrix invertibility theory and bounds for randomized permanent calculations, with connections to combinatorial probability. The large gap beyond the current exponential estimate justifies extreme difficulty.

## References

- V. H. Vu, *Recent progress in combinatorial random matrix theory*, Probability Surveys 18 (2021), 179–200, Conjecture 6.12 ([primary paper](https://arxiv.org/pdf/2005.02797); [journal](https://doi.org/10.1214/20-PS346)).
- Z. Hunter, M. Kwan and L. Sauermann, *Exponential anticoncentration of the permanent* (2025), Theorem 1.1 and §1.4 ([primary manuscript](https://arxiv.org/abs/2509.22577); [author PDF](https://mkwn.github.io/EAP.pdf)).

## Status check

Hunter–Kwan–Sauermann prove the displayed bound for one absolute positive constant, and explicitly identify Vu's stronger assertion as a future direction. Their result resolves exponential growth of the permanent range, which is not counted separately. Searches for Vu's conjecture, super-exponential permanent anticoncentration, and 2025–2026 found no complete resolution. The July 2026 [Ginibre-ensemble paper](https://arxiv.org/abs/2607.20329) treats Gaussian entries and does not establish the discrete Bernoulli assertion.

## Audit — 2026-09-10

Independently rechecked [Vu, Conjecture 6.12](https://arxiv.org/pdf/2005.02797) and [Hunter–Kwan–Sauermann, Theorem 1.1 and §1.4](https://arxiv.org/html/2509.22577); the latter's arXiv record still lists only its September 2025 version and explicitly leaves super-exponential decay open. The fixed-rate theorem is a weaker bound, so the status remains Open. Targeted later searches also checked the authors' [March 2026 finite-field paper, Theorems 1.3–1.4](https://arxiv.org/html/2603.15856) and the [July 2026 Gaussian paper](https://arxiv.org/abs/2607.20329): their different field or entry distribution does not prove this real Rademacher assertion. No complete resolution was located in this bounded search.
