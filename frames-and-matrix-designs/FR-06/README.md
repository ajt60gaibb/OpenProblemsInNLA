# FR-06 — Nonexistence of a complete set of mutually unbiased bases in dimension six

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Open  
**Last checked:** 2026-10-06

**Rating rationale:** Dimension six is the leading composite-dimension obstruction for mutually unbiased bases; its resolution would affect quantum measurements and structured matrix design.


Do there fail to exist seven matrices $`U_1,\ldots,U_7\in\mathbb C^{6\times6}`$ such that

```math
U_j^*U_j=I_6\quad(1\leq j\leq7),\qquad
|(U_j^*U_\ell)_{ab}|^2=\frac16
\quad(j\ne\ell,\ 1\leq a,b\leq6)?
```

Each $`U_j`$ is the matrix of an orthonormal basis; the second condition says the bases are pairwise mutually unbiased. The conjecture is $`\mathop{\mathrm{MUB}}\nolimits(6)<7`$. It is weaker than the often discussed assertion $`\mathop{\mathrm{MUB}}\nolimits(6)=3`$, and no claim about that sharper value is included here.

After fixing one basis as the standard basis, the problem becomes simultaneous feasibility of orthogonality and constant-modulus equations for six complex Hadamard matrices. It connects structured matrix construction, Gram matrix feasibility, and certified numerical search. Mutually unbiased measurements also provide well-conditioned quantum state reconstruction designs.

## References

1. A. S. Bandeira et al., *Randomstrasse 101: Open Problems of 2025*, arXiv:2603.29571 (2026), Conjecture 22. [Paper](https://arxiv.org/html/2603.29571v1).
2. D. McNulty and S. Weigert, *Mutually Unbiased Bases in Composite Dimensions — A Review*, Quantum 10 (2026), article 2051; arXiv:2410.23997v2, revised March 26, 2026. Sections 1 and 7 state and survey the dimension-six existence problem. [Paper](https://arxiv.org/abs/2410.23997).
3. M. Cárdenes Wuttig and J. Tindall, *A Complete Classification of Complex Hadamard Matrices of Order Six*, arXiv:2608.18053 (2026). Sections I and VI explicitly distinguish the claimed Hadamard classification from the still unsettled MUB problem. [Paper](https://arxiv.org/html/2608.18053).
4. Anonymous, *No Szöllősi matrix lies in a quadruplet of mutually unbiased bases in dimension six*, version 3.0-candidate, September 30, 2026. Unrefereed candidate with internal certificates for a restricted family. [Versioned deposit](https://doi.org/10.5281/zenodo.23051062), [versioned source](https://github.com/ipitchford/szollosi-mub-exclusion/tree/v3.0-candidate).

## Status check — 2026-09-10

Searched “mutually unbiased bases dimension six solved 2026” and “MUB 6 Hadamard classification”; inspected the current 2026 review and August 2026 classification. The latter explicitly states in its conclusion that its result does not settle mutually unbiased bases in $`\mathbb C^6`$. Numerical nonexistence searches for particular families do not exclude all seven-tuples above.

**Audit update (2026-09-10):** Rechecked the March 2026 MUB review and August Hadamard-classification paper, and searched for dimension-six resolutions. A classification of individual Hadamard matrices does not establish nonexistence of the required mutually unbiased tuple. This is a bounded literature check, not a proof that no solution exists.

## Literature update — 2026-10-06

The September 30 version 3.0-candidate of *No Szöllősi matrix lies in a quadruplet of mutually unbiased bases in dimension six* claims that no mutually unbiased quartet can contain both the standard basis and the columns of $`S/\sqrt6`$ when $`S`$ belongs to the specified closed two-circulant Szöllősi family. The source includes boundary cases in that family and supplies interval-arithmetic certificates and internal replay checks ([versioned deposit and manuscript](https://zenodo.org/records/23051062), [candidate source](https://github.com/ipitchford/szollosi-mub-exclusion/tree/v3.0-candidate)).

**Scope and remaining gap:** This is an unrefereed restricted-family candidate. The checked source does not record unaffiliated reproduction or end-to-end formal verification, and no certificate replay was performed for this update. Excluding quartets containing this family does not exclude every possible seven-tuple in the displayed statement; the manuscript's broader dimension-six implication depends on a separate conjecture. The full target therefore remains **Open**.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
