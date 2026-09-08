# FR-06 — Nonexistence of a complete set of mutually unbiased bases in dimension six

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Last checked:** 2026-09-08

**Status:** source-stated conjecture; no resolution found in screening on 2026-09-08.

Do there fail to exist seven matrices $U_1,\ldots,U_7\in\mathbb C^{6\times6}$ such that
$$
U_j^*U_j=I_6\quad(1\leq j\leq7),\qquad
|(U_j^*U_\ell)_{ab}|^2=\frac16
\quad(j\ne\ell,\ 1\leq a,b\leq6)?
$$
Each $U_j$ is the matrix of an orthonormal basis; the second condition says the bases are pairwise mutually unbiased. The conjecture is $\operatorname{MUB}(6)<7$. It is weaker than the often discussed assertion $\operatorname{MUB}(6)=3$, and no claim about that sharper value is included here.

After fixing one basis as the standard basis, the problem becomes simultaneous feasibility of orthogonality and constant-modulus equations for six complex Hadamard matrices. It connects structured matrix construction, Gram matrix feasibility, and certified numerical search. Mutually unbiased measurements also provide well-conditioned quantum state reconstruction designs.

## References

1. A. S. Bandeira et al., *Randomstrasse 101: Open Problems of 2025*, arXiv:2603.29571 (2026), Conjecture 22. [Paper](https://arxiv.org/html/2603.29571v1).
2. D. McNulty and S. Weigert, *Mutually Unbiased Bases in Composite Dimensions — A Review*, Quantum 10 (2026), article 2051; arXiv:2410.23997v2, revised March 26, 2026. Sections 1 and 7 state and survey the dimension-six existence problem. [Paper](https://arxiv.org/abs/2410.23997).
3. M. Cárdenes Wuttig and J. Tindall, *A Complete Classification of Complex Hadamard Matrices of Order Six*, arXiv:2608.18053 (2026). Sections I and VI explicitly distinguish the claimed Hadamard classification from the still unsettled MUB problem. [Paper](https://arxiv.org/html/2608.18053).

## Status check — 2026-09-08

Searched “mutually unbiased bases dimension six solved 2026” and “MUB 6 Hadamard classification”; inspected the current 2026 review and August 2026 classification. The latter explicitly states in its conclusion that its result does not settle mutually unbiased bases in $\mathbb C^6$. Numerical nonexistence searches for particular families do not exclude all seven-tuples above.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
