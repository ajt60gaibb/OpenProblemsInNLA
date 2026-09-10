# MD-05 — The sharp universal Spencer discrepancy constant

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Provenance:** source-stated extremal-value problem.  
**Status:** Open  
**Last checked:** 2026-09-10

**Rating rationale:** Determining the best constant across all sign matrices and all orders is a longstanding extremal discrepancy barrier; it sharpens a central matrix-balancing theorem.


For each positive integer $n$, define
$$
d_n=\frac{1}{\sqrt n}
\max_{A\in\{-1,1\}^{n\times n}}
\min_{x\in\{-1,1\}^n}\|Ax\|_\infty.
$$
Determine the exact value of
$$
C_*=\sup_{n\geq1}d_n.
$$
Thus $C_*$ is the smallest real constant for which every square sign matrix $A$ admits a column signing $x$ with $\|Ax\|_\infty\leq C_*\sqrt n$.

The question concerns the sharp worst-case error in simultaneous signed sums. In matrix form it asks how far a square sign matrix can keep all sign vectors from the coordinate cube of radius $C\sqrt n$.

The source also poses $\limsup_{n\to\infty}d_n>1$ as a related asymptotic conjecture. It is recorded here as context rather than counted as another entry.

## References

1. A. S. Bandeira, A. Kireeva, A. Maillard, and A. Rödder, *Randomstrasse101: Open Problems of 2024*, arXiv:2504.20539 (2025), entry 6, Open Problem 11, Conjecture 12, and the subsequent “Updates” paragraph. [Paper](https://arxiv.org/html/2504.20539v1).
2. A. S. Bandeira, *Did just a couple of deviations suffice all along? (problems 10–14)*, Randomstrasse101 (2024), the original statement of Open Problem 11. [Author's research post](https://randomstrasse101.math.ethz.ch/posts/HowManyDeviations/).
3. J. Spencer, *Ten Lectures on the Probabilistic Method*, second edition, SIAM (1994), Chapter 10, “Six Standard Deviations Suffice,” pp. 75–80, the classical universal-constant upper bound. [Chapter](https://epubs.siam.org/doi/10.1137/1.9781611970074.ch10).

## Status check — 2026-09-10

checked the current arXiv record, still 2504.20539v1 (2025-04-29), the source's update, and searches “Spencer sharp constant discrepancy” and “Spencer limsup discrepancy 2026”. The update refutes the stronger odd Sylvester–Hadamard claim in Conjecture 13; that claim is excluded. No resolution of Open Problem 11 or Conjecture 12 was found. Recent matrix Spencer results concern a different matrix-valued discrepancy problem.

**Audit update (2026-09-10):** Rechecked Open Problem 11 and the source’s update, then searched for exact Spencer constants. The refuted odd Sylvester–Hadamard claim is different. The all-order sharp supremum warrants extreme rather than hard. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
