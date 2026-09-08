# FR-09 — Complex equiangular tight frames with twice the dimension

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Last checked:** 2026-09-08

**Status:** source-backed open problem; no resolution found in the bounded literature check.

**Conjecture.** For every integer $d\ge2$, there exist $2d$ vectors $v_1,\ldots,v_{2d}\in\mathbb C^d$ satisfying
$$
\|v_i\|_2=1,\qquad
\sum_{i=1}^{2d}v_iv_i^*=2I_d,\qquad
|v_i^*v_j|^2=\frac1{2d-1}\quad(i\ne j).
$$
Thus the columns of $V=[v_1\ \cdots\ v_{2d}]$ form a unit-norm equiangular tight frame. The target requires every dimension, rather than only an infinite family.

These are optimal line configurations at redundancy two: their coherence attains the Welch bound. They provide well-balanced matrix designs for sensing and reconstruction. This is distinct from the $d^2$-vector SIC problem in FR-07.

## References

1. A. Glazyrin, *New constructions of optimal arrangements of $2d$ lines in $\mathbb C^d$*, August 2026, Conjecture 1 (attributed to Fallon and Iverson), and Sections 2–5 for constructions. [Paper](https://arxiv.org/abs/2608.16116).

## Status check — 2026-09-08

Glazyrin explicitly retains the all-dimension conjecture while extending the known constructions. Searches for the Fallon–Iverson conjecture and later redundancy-two ETF results found no full resolution. Finite dimension verification and the new tensor/power constructions do not cover the universal statement.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
