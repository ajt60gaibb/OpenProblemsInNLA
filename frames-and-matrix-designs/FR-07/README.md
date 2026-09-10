# FR-07 — Zauner's conjecture on maximal complex equiangular tight frames

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** All-dimension SIC existence is a central structured-design barrier connecting frame theory, quantum information and arithmetic geometry.


For every integer $d\geq2$, do there exist $d^2$ unit vectors $\phi_1,\ldots,\phi_{d^2}\in\mathbb C^d$ satisfying
$$
|\phi_i^*\phi_j|^2=\frac1{d+1}\quad(i\ne j),
\qquad
\sum_{i=1}^{d^2}\phi_i\phi_i^*=dI_d?
$$
This is existence of an equiangular tight frame with $d^2$ vectors in $\mathbb C^d$, equivalently a symmetric informationally complete positive operator-valued measure after dividing the rank-one projectors by $d$. The statement concerns existence in every dimension. It does not impose additional Weyl–Heisenberg or order-three symmetry.

These frames attain the optimal coherence for $d^2$ unit vectors and lead to highly symmetric Gram matrices. Their construction is a concrete structured matrix design and conditioning problem with applications to state reconstruction. Exact all-dimension existence remains substantially stronger than numerical constructions in many individual dimensions.

## References

1. A. S. Bandeira et al., *Randomstrasse 101: Open Problems of 2025*, arXiv:2603.29571 (2026), Conjecture 24 and its definition of equiangular tight frames. [Paper](https://arxiv.org/html/2603.29571v1).
2. M. Appleby, S. T. Flammia, and G. S. Kopp, *A Constructive Approach to Zauner's Conjecture via the Stark Conjectures*, arXiv:2501.03970v2 (2025). The abstract and main construction distinguish conjectural/conditional arithmetic input from unconditional all-dimension existence. [Paper](https://arxiv.org/abs/2501.03970).
3. S. Joka, *Symmetric Informationally Complete Positive Operator Valued Measure and Zauner conjecture*, arXiv:2601.13475v5. Cited only as an excluded proof claim: withdrawn May 31, 2026, with the author's comment that the proof is incorrect. [Withdrawal record](https://arxiv.org/abs/2601.13475).

## Status check — 2026-09-10

Searched “Zauner conjecture proof 2026”, “SIC POVM all dimensions solved”, and checked the latest versions rather than relying on search snippets. The apparent January 2026 proof claim is withdrawn; its unchanged abstract must not be read as a valid solution. The Appleby–Flammia–Kopp construction does not give an unconditional proof of the statement. No other general resolution was found.

**Audit update (2026-09-10):** Rechecked the Appleby–Flammia–Kopp conditional construction and Joka’s withdrawn v5, and searched for other general proofs. Many individual dimensions have exact constructions, but the all-dimension existence question remains unresolved; the withdrawn claim is not a solution. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
