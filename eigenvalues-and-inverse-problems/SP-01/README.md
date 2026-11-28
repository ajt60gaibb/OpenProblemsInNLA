# SP-01 — The sharp generic threshold for spectral-subspace rotation

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-11-28  

**Rating rationale:** Challenging reflects a sharp perturbation threshold without geometric separation assumptions beyond a spectral gap; community impact is the stability of spectral subspaces.

Let $`A`$ be a self-adjoint, possibly unbounded operator on a separable complex Hilbert space. Suppose $`\sigma(A)=\sigma\cup\Sigma`$, where the two nonempty closed sets satisfy $`d=\mathop{\mathrm{dist}}\nolimits(\sigma,\Sigma)>0`$. For a bounded self-adjoint perturbation $`V`$, set

```math
P=E_A(\sigma),\qquad Q=E_{A+V}(O_{d/2}(\sigma)),\qquad
O_r(S)=\{x\in\mathbb R:\mathop{\mathrm{dist}}\nolimits(x,S)< r\},
```

where $`E_B`$ denotes the spectral projection measure of $`B`$.

Does $`\|V\|< d/2`$ always imply $`\|P-Q\|<1`$? All norms are operator norms. Equivalently, is the optimal universal constant $`c_{\mathrm{opt}}=1/2`$ for guaranteeing that the maximal angle $`\arcsin\|P-Q\|`$ is strictly below $`\pi/2`$?

The two spectral sets may interlace: no ordering or disjoint-convex-hull hypothesis is imposed. The source's operator formulation is retained; Hermitian matrix invariant-subspace perturbation is its finite-dimensional setting. This problem concerns subspace orientation after perturbation, beyond preservation of a spectral gap.

## Sharp threshold for rank-two perturbations — 2026-11-28

**Partial result (AI-derived).** The half-gap guarantee holds for every
self-adjoint perturbation of rank at most two, including indefinite
perturbations and unbounded $`A`$. More generally, under $`\|V\|< d/2`$
it holds whenever

```math
\|V\|_{\mathrm{HS}}<\sqrt{2}\,(d-\|V\|),
```

where $`\|\cdot\|_{\mathrm{HS}}`$ is the Hilbert–Schmidt norm. No
placement condition on the spectral sets is required. The unrestricted
threshold remains open. The earlier rank-one result for bounded $`A`$
uses a determinant identity. [Gebert, Theorem 2.10](https://arxiv.org/abs/1705.02796).

**Hilbert–Schmidt projection estimate.** Suppose self-adjoint $`S,T`$
differ by a bounded Hilbert–Schmidt operator $`W=T-S`$. Let $`E,F`$
be their respective spectral projections onto selected components.
Assume each selected component has distance at least $`g>0`$ from
the other operator's complementary component. Then

```math
\|E-F\|_{\mathrm{HS}}^2
=\|E(I-F)\|_{\mathrm{HS}}^2+\|(I-E)F\|_{\mathrm{HS}}^2
\le \frac{\|W\|_{\mathrm{HS}}^2}{g^2}.
```

Indeed, $`E(I-F)`$, regarded as an operator from $`\mathop{\mathrm{ran}}\nolimits(I-F)`$
to $`\mathop{\mathrm{ran}}\nolimits E`$, solves the weak Sylvester equation with
left operator $`S|_{\mathop{\mathrm{ran}}\nolimits E}`$, right operator
$`T|_{\mathop{\mathrm{ran}}\nolimits(I-F)}`$, and forcing $`-EW(I-F)`$.
The analogous forcing for $`(I-E)F`$ is $`-(I-E)WF`$. On the Hilbert
space of Hilbert–Schmidt operators the joint spectral calculus for
left and right multiplication solves each equation by applying the
multiplier $`(s-t)^{-1}`$ to its forcing. The joint spectral projections
on rectangles act by compression with the left and right spectral
projections. The multiplier is bounded by $`1/g`$ and the resulting
operator satisfies the weak equation by testing on the two domains.
A bounded homogeneous weak solution intertwines both resolvents and
therefore both spectral measures. Disjoint left and right spectra force
that solution to vanish. This identifies the Hilbert–Schmidt solutions
with the displayed projection products. The two forcing blocks have
orthogonal left and right supports, so their squared norms sum to at
most $`\|W\|_{\mathrm{HS}}^2`$.

**First possible right angle.** Write $`v=\|V\|`$ and use the path
$`Q_t=E_{A+tV}(O_{d/2}(\sigma))`$ for $`0\le t\le1`$. The usual
spectral inclusion for bounded self-adjoint perturbations places the
two components within distance $`tv`$ of $`\sigma,\Sigma`$,
respectively. Thus the cross distances for times $`s,t`$ are at least
$`d-(s+t)v\ge d-2v`$. The estimate applied to $`(t-s)V`$ shows that
$`t\mapsto Q_t`$ is continuous in Hilbert–Schmidt differences. Applied
from time zero it gives $`\|P-Q_t\|_{\mathrm{HS}}\le t\|V\|_{\mathrm{HS}}/(d-tv)<\sqrt2`$.

Whenever $`\|P-Q_t\|<1`$, the two directed gaps
$`\|P(I-Q_t)\|`$ and $`\|(I-P)Q_t\|`$ coincide. In fact,
$`P|_{\mathop{\mathrm{ran}}\nolimits Q_t}`$ is invertible onto $`\mathop{\mathrm{ran}}\nolimits P`$
because both it and its adjoint are bounded below. Its polar
decomposition identifies the two squared gap operators. Consequently,
at a first time with $`\|P-Q_t\|=1`$, continuity would make both
directed gaps equal to one. Their squared Hilbert–Schmidt norms would
sum to at least two, a contradiction.

For rank at most two, $`\|V\|_{\mathrm{HS}}\le\sqrt2\,v`$ verifies
the sufficient condition whenever $`v< d/2`$. Sharpness in this class
follows from $`A=\mathop{\mathrm{diag}}\nolimits(0,d)`$, $`\sigma=\{0\}`$ and
$`V=\mathop{\mathrm{diag}}\nolimits(d/2,-d/2)`$. At equality the open interval
$`O_{d/2}(\sigma)`$ excludes the eigenvalue $`d/2`$ of $`A+V`$ and
$`\|P-Q\|=1`$.

## References

 A. Seelmann, *Notes on the subspace perturbation problem for off-diagonal perturbations*, Proceedings AMS 144 (2016), 3825–3832, introduction p.3826, the paragraph on general perturbations ([primary manuscript](https://arxiv.org/pdf/1412.6294); [journal](https://doi.org/10.1090/proc/13118)). Seelmann, *On an estimate in the subspace perturbation problem*, Journal d'Analyse Mathématique 135 (2018), 313–343 ([primary manuscript](https://arxiv.org/abs/1310.4360)). Seelmann, *Unifying the treatment of indefinite and semidefinite perturbations in the subspace perturbation problem*, Operators and Matrices 15 (2021), 1181–1188, Theorems 1.1–1.2 ([primary paper](https://files.ele-math.com/articles/oam-15-74.pdf)).

## Status check — 2026-09-08

 The 2021 generic theorem retains the sufficient constant $`c_{\mathrm{crit}}=0.4548399\ldots`$; its sharp theorem at a larger threshold assumes extra spectral separation. The 2018 paper's solved optimization problem determines an upper angle bound, not the conjectured threshold. Searches for “subspace perturbation”, “optimal constant”, “1/2”, “Seelmann”, “conjecture”, and 2024–2026 found no resolution. No recent explicit reaffirmation of the exact endpoint conjecture was located; the status evidence is bounded.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

## Audit update — 2026-09-10

Rechecked [Seelmann's primary account](https://arxiv.org/pdf/1412.6294) and the [2021 perturbation paper](https://files.ele-math.com/articles/oam-15-74.pdf). The generic sharp threshold remains distinct from the established sufficient constants and stronger results under extra geometry. Searches for subsequent optimal generic subspace-rotation thresholds found no solution; these nonsharp estimates do not complete the displayed optimum.
