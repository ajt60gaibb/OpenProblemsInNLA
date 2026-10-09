# RA-06 — Sensitivity-dependent row sampling for $`\ell_p`$ embeddings when p exceeds two

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because ordinary sensitivities must control all directions with nearly linear total-sensitivity cost; community impact is instance-sensitive regression and subspace sketching.  
**Last checked:** 2026-09-30  

**Status:** Solved  

## Statement

Fix $`p>2`$. For a full-column-rank matrix $`A\in\mathbb R^{n\times d}`$, with rows $`a_i^T`$, set

```math
s_i=\sup_{x\ne0}\frac{|a_i^Tx|^p}{\|Ax\|_p^p},\qquad
\mathcal S=\sum_{i=1}^n s_i.
```

For a scalar $`\alpha>0`$, retain row $`i`$ independently with probability

```math
q_i=\min\{1,1/n+s_i/\alpha\},
```

and scale each retained row by $`q_i^{-1/p}`$; let $`\widetilde A`$ be the resulting matrix.

Do constants $`C_p,c_p>0`$ exist such that, for every $`A`$ and $`0<\varepsilon,\delta<1/2`$, one can choose $`\alpha`$ with

```math
\sum_iq_i\leq C_p\varepsilon^{-2}(\mathcal S+d)
\log^{c_p}\!\left(\frac{2nd}{\varepsilon\delta}\right),
```

while, with probability at least $`1-\delta`$,

```math
(1-\varepsilon)\|Ax\|_p^p\leq\|\widetilde Ax\|_p^p
\leq(1+\varepsilon)\|Ax\|_p^p
\qquad\text{for all }x\in\mathbb R^d?
```

The size is the expected number of retained rows. The question concerns this independent sampling rule based on the ordinary $`\ell_p`$ sensitivities, not arbitrary row weights or augmented sensitivities.

This would exploit easy instances through total sensitivity rather than using the worst-case dimension-only bound. It applies directly to sketching $`\ell_p`$ regression and other computations on the column space of $`A`$. The p>2 ordinary-sensitivity theorem of Woodruff–Yasuda has size $`\widetilde O_p(\varepsilon^{-2}\mathcal S^{2-2/p})`$.

## Resolution — 2026-09-30

**Negative resolution for every fixed real exponent** $`p>2`$. Theorem 5.1 of [*An Accuracy Obstruction for lp Row Sparsification: A Complete-Graph Counterexample to RA-06*](../../references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.pdf) ([LaTeX source](../../references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.tex)), dated 30 September 2026, refutes the original expected-size guarantee with exactly its ordinary sensitivities, independent retention rule, rescaling and simultaneous norm-power preservation.

The grounded incidence matrix of the complete graph on $`v`$ vertices has $`n=\binom v2`$, $`d=v-1`$, and equal row sensitivities

```math
s_i=\frac1{1+(v-2)2^{1-p}},\qquad \mathcal S=\Theta_p(d).
```

Under $`v-1\ge6^{-p}\varepsilon^{-(p+1)}`$, Corollary 4.2 forces expected sample size $`\Omega_p((\mathcal S+d)\varepsilon^{-p})`$ even for one successful realization of the prescribed common-probability sampler. Taking $`\varepsilon=b^{-1}`$, $`\delta=1/4`$ and $`v=\lceil b^{p+2}\rceil`$ contradicts every fixed polylogarithmic multiplier of the proposed quadratic inverse-accuracy budget. The floor and saturation in the original rule are included.

Theorem 3.1 and Corollary 3.2 also give a support obstruction for arbitrary nonnegative reweighted row subsets, with a success-probability factor for randomized expected support. The obstruction concerns accuracy dependence in an explicit growing-dimension regime; it does not rule out nearly linear sensitivity dependence at fixed accuracy and does not concern unrestricted linear sketches.

**Attribution and review.** The original conjecture and sampling model are credited to Woodruff–Yasuda, Section 3 and Definition 1.1/Theorem 1.5. **No novelty or priority is claimed for this local manuscript.** The supplied [ChatGPT 6 Pro audit](https://chatgpt.com/share/6abd3ea9-6310-83ed-8d37-edc449055572) reports that the mathematical core refutes RA-06 and derives the arbitrary-weight strengthening. Its follow-up revision incorporates that strengthening, direct attribution, the explicit dimension regime and the requested presentation fixes. This is an informal AI audit, not external human peer review or formal proof-assistant certification. See the [submission record](../../references/haidary-resolutions-2026-09-30/README.md). Historical ratings are retained, and the original target is retained above.

## References

1. D. P. Woodruff and T. Yasuda, *Sharper Bounds for $`\ell_p`$ Sensitivity Sampling*.  
   ICML 2023, arXiv:2306.00732v2. Definition 1.1 fixes the sampling model, Theorem 1.5 gives the p>2 bound, and Section 3 explicitly conjectures $`\widetilde O(\varepsilon^{-2}(\mathcal S+d))`$. [Paper](https://arxiv.org/html/2306.00732v2).
2. A. Munteanu and S. Omlor, *Optimal bounds for $`\ell_p`$ sensitivity sampling via $`\ell_2`$ augmentation*.  
   ICML 2024, PMLR 235, pp. 36769–36796. Question 1.2 and Section 1.1 distinguish the solved/obstructed p≤2 situation from the remaining p>2 case. [Paper](https://arxiv.org/abs/2406.00328).
3. R. Chhaya, A. Dasgupta, D. Feldman, and S. Shit, *Deterministic Coreset for Lp Subspace*.  
   arXiv:2601.00361 (2026). This claimed deterministic embedding result was withdrawn on May 15, 2026 because some proofs are incomplete; it is cited only to prevent a stale abstract from being mistaken for a resolution. [Paper](https://arxiv.org/abs/2601.00361).

## Status check — 2026-09-08

Searched “p>2 sensitivity sampling conjecture 2025 2026”, “sensitivity sampling S+d”, and the exact paper titles; checked the current arXiv records. No resolution of the stated p>2 rule was found. Results using $`\ell_2`$ augmentation for p≤2 do not settle it. The 2026 deterministic embedding claim was withdrawn (latest v3, May 15, 2026), so its abstract is not evidence that any open case has been resolved.

## Audit — 2026-09-10

Rechecked [Woodruff–Yasuda, §3](https://arxiv.org/html/2306.00732v2) and the [augmentation paper's scope](https://arxiv.org/abs/2406.00328). The ordinary-sensitivity $`p>2`$ target remains unresolved in these sources. Sensitivity-sampling follow-up searches found no resolution. Difficulty was raised to reflect the general uniform sampling obstruction.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
