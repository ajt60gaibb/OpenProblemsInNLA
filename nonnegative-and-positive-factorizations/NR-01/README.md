# NR-01 — Exact nonnegative rank of regular polygon slack matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because matching lower bounds must hold for every polygon size despite an explicit upper construction; community importance connects structured NMF with optimal linear extended formulations.  
**Status:** Partially resolved  
**Area:** structured nonnegative matrix factorization  
**Last checked:** 2026-09-13

## Context and notation

All factorizations are over the real numbers. For
$`X\in\mathbb R_{\ge0}^{m\times n}`$, define

```math
\mathop{\mathrm{rank}}\nolimits_+(X)=\min\{r\ge0:X=WH,\quad
W\in\mathbb R_{\ge0}^{m\times r},\ H\in\mathbb R_{\ge0}^{r\times n}\}.
```

## Problem statement

For each integer $`n\ge3`$, define the $`n\times n`$ nonnegative matrix

```math
S_n(i,j)=\cos(\pi/n)-\cos\bigl((2i+1-2j)\pi/n\bigr),
\qquad 0\le i,j< n.
```

It is the slack matrix obtained from the vertices of the regular $`n`$-gon on
the unit circle and its supporting facet inequalities.

### Question

With $`k=\lceil\log_2 n\rceil`$, is it true for every $`n\ge3`$ that

```math
\mathop{\mathrm{rank}}\nolimits_+(S_n)=
\begin{cases}
2k-1,&2^{k-1}< n\le 2^{k-1}+2^{k-2},\\
2k,&2^{k-1}+2^{k-2}< n\le2^k?
\end{cases}
```

## References

Arnaud Vandaele, Nicolas Gillis, François Glineur, and Daniel
Tuyttens, [*Heuristics for Exact Nonnegative Matrix Factorization*](https://arxiv.org/html/1411.7245),
Journal of Global Optimization **65** (2016), 369–400, §6.2, Conjecture 2.
Vandaele, Gillis, and Glineur,
[*On the Linear Extension Complexity of Regular n-gons*](https://arxiv.org/abs/1505.08031),
Linear Algebra and its Applications **521** (2017), 217–239, proves the
corresponding upper bound. Nicolas Gillis,
[*Nonnegative Matrix Factorization*](https://orbi.umons.ac.be/bitstream/20.500.12907/42337/1/NMFbook_SIAM_reprint.pdf),
SIAM, 2020, §3.6.3.4, p. 90.

## Status check — 2026-09-10

Rechecked [Baeckelant–Vandaele–Gillis v2, Appendix A.2, Table 7](https://arxiv.org/html/2605.14058v2), and searched for later regular-polygon rank resolutions. The conjectured value is attained and proved for substantive ranges, including n from 5 through 16, but gaps remain, for example at n=17. The upper formula remains conjecturally sharp for the whole family; no full resolution was located.


## Reviewed partial result — 2026-09-13

Sidney Holden (Center for Computational Biology, Flatiron Institute, Simons
Foundation) proves in [Theorem 1.1](../../references/holden-nr01-2026-09-13/report.pdf)
that

```math
\mathop{\mathrm{rank}}\nolimits_+(S_n)=9,\qquad n=17,18,19,20.
```

The computer-assisted lower bound covers arbitrary real factorizations, including
nonsimple lifts and nongeneric projections; exact nine-term factorizations give
the matching upper bounds. Sections 2–7 supply the rank-balance reduction,
finite shadow cover, degeneration argument and characteristic-zero justification
of the modular rank certificates. The argument also gives the lower bound nine
for every size at least 21 by the eight-facet vertex bound in Section 2; together
with the known upper construction this settles sizes 21–24.

The [independent informal Codex AI-agent audit](../../references/holden-nr01-2026-09-13/independent-review.md)
checks the mathematical reductions and reproduces the complete computational
pipeline. This is partial affirmative progress: the original equality for every
size remains open, beginning with $`9\le\mathop{\mathrm{rank}}\nolimits_+(S_{25})\le10`$.
In particular, sizes 25–30 and 33–42 remain unresolved by this submission;
no general formula for the remaining sizes is proved. **NR-01 remains Partially
resolved.** No Lean verification or external human peer review is claimed.

[Submission, reproducibility and verified affiliation](../../references/holden-nr01-2026-09-13/README.md)
· [Editable manuscript](../../references/holden-nr01-2026-09-13/report.tex).
The original ID, canonical path, target and prior references are retained.
