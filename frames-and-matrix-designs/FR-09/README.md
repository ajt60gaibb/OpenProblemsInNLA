# FR-09 — Complex equiangular tight frames with twice the dimension

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** All-dimension redundancy-two ETF existence is a difficult exact-design barrier; its direct impact is in frame theory, sensing and reconstruction.


<!-- colbrook-frames -->
## Reviewed submission - 2026-09-11

Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge.

The supplied rational certificates independently pass the exact interval contraction test in dimensions $`d=166,209,256,1505`$. The accompanying proof, Sections 1-4, constructs Hermitian conference matrices of order $`2d`$ and hence unit-norm complex equiangular tight frames with $`2d`$ vectors. This records four certified instances, not all dimensions or an asserted priority claim. The other 88 dimensions appearing only in the supplied catalog report lack certificates in this archive and are not certified by this submission.

See the [certificate proof](../../references/colbrook-frames-2026-09-11/conference-proof.md), [independent agent review](../../references/colbrook-frames-2026-09-11/verification/reviews/FR-09-review.md), and [reproducible submission record](../../references/colbrook-frames-2026-09-11/README.md). Independent agent review is not external human peer review or formal proof-assistant certification. Original problem, ratings and historical audits are retained below.
<!-- /colbrook-frames -->

**Conjecture.** For every integer $`d\ge2`$, there exist $`2d`$ vectors $`v_1,\ldots,v_{2d}\in\mathbb C^d`$ satisfying

```math
\|v_i\|_2=1,\qquad
\sum_{i=1}^{2d}v_iv_i^*=2I_d,\qquad
|v_i^*v_j|^2=\frac1{2d-1}\quad(i\ne j).
```

Thus the columns of $`V=[v_1\ \cdots\ v_{2d}]`$ form a unit-norm equiangular tight frame. The target requires every dimension, rather than only an infinite family.

These are optimal line configurations at redundancy two: their coherence attains the Welch bound. They provide well-balanced matrix designs for sensing and reconstruction. This is distinct from the $`d^2`$-vector SIC problem in FR-07.

## References

1. A. Glazyrin, *New constructions of optimal arrangements of $`2d`$ lines in $`\mathbb C^d`$*, August 2026, Conjecture 1 (attributed to Fallon and Iverson), and Sections 2–5 for constructions. [Paper](https://arxiv.org/abs/2608.16116).

2. K. Fallon and J. W. Iverson, *On the optimal arrangement of $`2d`$ lines in $`\mathbb C^d`$*, Information and Inference 14(2) (2025), iaaf008. [Published paper](https://doi.org/10.1093/imaiai/iaaf008).

## Status check — 2026-09-10

Glazyrin explicitly retains the all-dimension conjecture while extending the known constructions. Searches for the Fallon–Iverson conjecture and later redundancy-two ETF results found no full resolution. Finite dimension verification and the new tensor/power constructions do not cover the universal statement.

**Audit update (2026-09-10):** Rechecked Glazyrin’s Conjecture 1 and construction discussion, and searched for later Fallon–Iverson results. Added the original published conjecture source. Explicit families provide partial cases, not every dimension. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
