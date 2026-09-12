# MF-03 — A uniform disk bound for wave-kernel Padé approximants

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** hard  
**Importance:** interesting to specialist  
**Rating rationale:** Hard because this is a focused all-orders Padé inequality within established approximation theory; its immediate impact is on specialist wave-kernel error analysis.  
**Status:** Solved  
**Last checked:** 2026-09-11  

<!-- colbrook-matrix-functions -->
## Resolution — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the exact target.**

For every integer $`m\ge1`$, the normalized diagonal Padé denominator for $`\cosh\sqrt z`$ is nonzero on $`|z|\le3`$ and $`|1-r_m(z)|\le2`$ there. The bound is strict for $`m\ge2`$ and sharp for $`m=1`$ at $`z=3`$. The analytic tail argument and exact finite certificates cover every order.

The complete target is resolved. Its former difficulty rating is historical; the original statement, references and dated audits remain below.

**Primary reference:** [complete authored PDF](../../references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.pdf), [standalone TeX](../../references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex), **Theorem 1**. [Independent proof review](../../references/colbrook-matrix-functions-2026-09-11/verification/reviews/MF-03-review.md) · [Authorship and submission record](../../references/colbrook-matrix-functions-2026-09-11/README.md). Verification is independent agent review, not external human peer review or formal certification.

<!-- /colbrook-matrix-functions -->

## Problem statement

Let

```math
f(z)=\sum_{j=0}^\infty\frac{z^j}{(2j)!}=\cosh\sqrt z,
```

where the series defines the entire function without a square-root branch choice.
For each integer $`m\ge1`$, let $`r_m=P_m/Q_m`$ be its diagonal Padé
approximant at zero: $`\deg P_m,\deg Q_m\le m`$, $`Q_m(0)=1`$, and
$`Q_m(z)f(z)-P_m(z)=O(z^{2m+1})`$. Is it true that the reduced rational
function $`r_m`$ has no pole in $`\{z\in\mathbb C:|z|\le3\}`$ and

```math
|1-r_m(z)|\le2\qquad (|z|\le3)
```

for every $`m`$?

## Reference and status evidence

Nadukandi and Higham,
[Computing the Wave-Kernel Matrix Functions](https://eprints.maths.manchester.ac.uk/2651/3/manuscript_nadukandi_higham_wkm_2018_08_01.pdf),
SIAM J. Scientific Computing 40(6) (2018),
[DOI](https://doi.org/10.1137/18M1170352), §4.2, Conjecture 4.6,
manuscript p. 12. Lemma 4.5 establishes the finite range $`m\le20`$;
§4.3 explains its role in backward-error analysis. Searches for the paper title
with “conjecture” and for “Conjecture 4.6” with “cosh” and “Padé” located no
general proof or counterexample. The status evidence is therefore weaker than a
recent paper explicitly reaffirming the conjecture.

## Audit — 2026-09-10

Rechecked [Lemma 4.5 and Conjecture 4.6](https://eprints.maths.manchester.ac.uk/2651/3/manuscript_nadukandi_higham_wkm_2018_08_01.pdf): the displayed assertion is proved for $`1\le m\le20`$, while arbitrary $`m`$ remains conjectural. Paper-title and conjecture-number searches found no general resolution. The open portion still rests on historical primary evidence.
