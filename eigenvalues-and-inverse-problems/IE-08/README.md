# IE-08 — A cubic-time Schur algorithm using logarithmic precision

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Open  
**Last checked:** 2026-09-10  

**Rating rationale:** Extreme reflects an end-to-end precision and complexity theorem for general Schur decomposition; broad impact is justified by this central eigenvalue-computation task.

## Problem statement

Does a randomized floating-point algorithm exist with the following guarantee? Given $A\in\mathbb C^{n\times n}$, $\|A\|_2\leq1$, and $0<\delta<1/2$, it uses at most

$$
O(n^3\log^c(n/\delta))\quad\text{arithmetic operations and}\quad
O(\log(n/\delta))\quad\text{mantissa bits}
$$

and, with probability at least $0.99$, returns an upper triangular $T$ and $Q$ satisfying

$$
\|A-QTQ^*\|_2\leq\delta,
\qquad \|Q^*Q-I\|_2\leq\delta?
$$

The constants and exponent $c$ must be universal, with no additional eigenvalue-separation or diagonalizability assumption. Use the usual relative-error floating-point model, with sufficient exponent range to avoid overflow and underflow. This is a statement about the precision needed for a rigorous algorithm, not whether ordinary QR implementations usually work well.

## References

Amsel et al., [*Linear Systems and Eigenvalue Problems*](https://arxiv.org/html/2602.05394v3#S3.SS2), Problem 3.3. Schneider, [*Pseudospectral Divide-and-Conquer for the Generalized Eigenvalue Problem*](https://escholarship.org/content/qt3bb8s95w/qt3bb8s95w_noSplash_22c8cf7d2873d111b5bb367d09dc40fc.pdf), dissertation, §1.6.1 and Chapter 6. Banks et al., [FOCM diagonalization paper](https://doi.org/10.1007/s10208-022-09577-5), §6, precision-reduction question.

## Earlier status check — 2026-09-08

Searches for `Schur logarithmic precision 2026` and `site:arxiv.org Schur precision 2026` found no complete analysis meeting both bounds. The dissertation explicitly distinguishes analyzed subroutines from an end-to-end precision theorem.

## Audit update — 2026-09-10

Rechecked [workshop version 3](https://arxiv.org/html/2602.05394v3), Problem 3.3 and its update. The report still distinguishes algorithmic ingredients from a complete logarithmic-precision analysis. Targeted cubic-Schur and precision searches found no theorem meeting every displayed requirement.
