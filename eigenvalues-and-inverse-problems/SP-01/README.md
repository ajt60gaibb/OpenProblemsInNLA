# SP-01 — The sharp generic threshold for spectral-subspace rotation

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-10  

**Rating rationale:** Challenging reflects a sharp perturbation threshold without geometric separation assumptions beyond a spectral gap; community impact is the stability of spectral subspaces.

Let $`A`$ be a self-adjoint, possibly unbounded operator on a separable complex Hilbert space. Suppose $`\sigma(A)=\sigma\cup\Sigma`$, where the two nonempty closed sets satisfy $`d=\mathop{\mathrm{dist}}\nolimits(\sigma,\Sigma)>0`$. For a bounded self-adjoint perturbation $`V`$, set

```math
P=E_A(\sigma),\qquad Q=E_{A+V}(O_{d/2}(\sigma)),\qquad
O_r(S)=\{x\in\mathbb R:\mathop{\mathrm{dist}}\nolimits(x,S)<r\},
```

where $`E_B`$ denotes the spectral projection measure of $`B`$.

Does $`\|V\|<d/2`$ always imply $`\|P-Q\|<1`$? All norms are operator norms. Equivalently, is the optimal universal constant $`c_{\mathrm{opt}}=1/2`$ for guaranteeing that the maximal angle $`\arcsin\|P-Q\|`$ is strictly below $`\pi/2`$?

The two spectral sets may interlace: no ordering or disjoint-convex-hull hypothesis is imposed. The source's operator formulation is retained; Hermitian matrix invariant-subspace perturbation is its finite-dimensional setting. This problem concerns subspace orientation after perturbation, beyond preservation of a spectral gap.

## References

 A. Seelmann, *Notes on the subspace perturbation problem for off-diagonal perturbations*, Proceedings AMS 144 (2016), 3825–3832, introduction p.3826, the paragraph on general perturbations ([primary manuscript](https://arxiv.org/pdf/1412.6294); [journal](https://doi.org/10.1090/proc/13118)). Seelmann, *On an estimate in the subspace perturbation problem*, Journal d'Analyse Mathématique 135 (2018), 313–343 ([primary manuscript](https://arxiv.org/abs/1310.4360)). Seelmann, *Unifying the treatment of indefinite and semidefinite perturbations in the subspace perturbation problem*, Operators and Matrices 15 (2021), 1181–1188, Theorems 1.1–1.2 ([primary paper](https://files.ele-math.com/articles/oam-15-74.pdf)).

## Status check — 2026-09-08

 The 2021 generic theorem retains the sufficient constant $`c_{\mathrm{crit}}=0.4548399\ldots`$; its sharp theorem at a larger threshold assumes extra spectral separation. The 2018 paper's solved optimization problem determines an upper angle bound, not the conjectured threshold. Searches for “subspace perturbation”, “optimal constant”, “1/2”, “Seelmann”, “conjecture”, and 2024–2026 found no resolution. No recent explicit reaffirmation of the exact endpoint conjecture was located; the status evidence is bounded.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

## Audit update — 2026-09-10

Rechecked [Seelmann's primary account](https://arxiv.org/pdf/1412.6294) and the [2021 perturbation paper](https://files.ele-math.com/articles/oam-15-74.pdf). The generic sharp threshold remains distinct from the established sufficient constants and stronger results under extra geometry. Searches for subsequent optimal generic subspace-rotation thresholds found no solution; these nonsharp estimates do not complete the displayed optimum.
