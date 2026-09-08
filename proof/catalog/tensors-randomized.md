# Tensors, low-rank approximation, and randomized linear algebra

> Legacy source map and screening notes. Admitted statements have moved to category/problem folders. Follow the links below or [browse the new index](../../CATALOG.md). Shared notation and uncounted material are retained here as the historical source record.

This file contains **8 admitted problems**. Labels are editorial assessments, not ratings supplied by the cited authors. “Open” means an explicit published question or conjecture was located and a search for subsequent resolutions found none that covers the stated assumptions. It does not certify that no resolution exists. All status searches below were performed on **2026-09-08**; the dates of the underlying evidence are recorded separately.

<a id="tr-01"></a>

## TR-01 — Optimal dimension for a rerandomized Hadamard embedding

[Open the problem folder](../../randomized-and-low-rank-approximation/TR-01/README.md) · [PDF](../../randomized-and-low-rank-approximation/TR-01/problem.pdf) · [LaTeX](../../randomized-and-low-rank-approximation/TR-01/problem.tex)


<a id="tr-03"></a>

## TR-03 — Sharp gap between volume sampling and the worst matrix with a prescribed spectrum

[Open the problem folder](../../randomized-and-low-rank-approximation/TR-03/README.md) · [PDF](../../randomized-and-low-rank-approximation/TR-03/problem.pdf) · [LaTeX](../../randomized-and-low-rank-approximation/TR-03/problem.tex)


<a id="tr-04"></a>

## TR-04 — Improve the worst-case approximation factor for prescribed tensor-train ranks

[Open the problem folder](../../tensor-computations/TR-04/README.md) · [PDF](../../tensor-computations/TR-04/problem.pdf) · [LaTeX](../../tensor-computations/TR-04/problem.tex)


### Shared probability model for TR-05 and TR-06

Fix $d\ge3$, $n_j\ge2$, and $r\ge2$. Assume generic complex identifiability: outside a proper algebraic exceptional set, a complex tensor of rank $r$ in this format has a unique unordered collection of $r$ rank-one summands. Let $M_r$ be the smooth identifiable locus of real rank-$r$ tensors, with induced Euclidean volume $dV$. The random input has density

$$
d\mu(A)=Z^{-1}e^{-\|A\|_F^2/2}\,dV(A).
$$

For the addition map $\Phi(a_1,\ldots,a_r)=\sum_i a_i$ on rank-one tensors, let $\Psi$ be a local inverse at $A$. Use Frobenius norms and their product norm. Define

$$
\kappa(A)=\|D\Psi(A)\|_2,\qquad
\kappa_{\rm ang}(A)=\|D(p^{\times r}\circ\Psi)(A)\|_2,
\quad p(a)=a/\|a\|_F.
$$

Values on measure-zero exceptional sets do not affect the expectations. This samples tensors by volume, not independent Gaussian summands.

<a id="tr-05"></a>

## TR-05 — Infinite mean condition number in every identifiable tensor format

[Open the problem folder](../../tensor-computations/TR-05/README.md) · [PDF](../../tensor-computations/TR-05/problem.pdf) · [LaTeX](../../tensor-computations/TR-05/problem.tex)


<a id="tr-06"></a>

## TR-06 — Finite mean angular condition number for identifiable tensor decomposition

[Open the problem folder](../../tensor-computations/TR-06/README.md) · [PDF](../../tensor-computations/TR-06/problem.pdf) · [LaTeX](../../tensor-computations/TR-06/problem.tex)


<a id="tr-07"></a>

## TR-07 — Random column subsets of arbitrary fixed-sparsity matrices

[Open the problem folder](../../randomized-and-low-rank-approximation/TR-07/README.md) · [PDF](../../randomized-and-low-rank-approximation/TR-07/problem.pdf) · [LaTeX](../../randomized-and-low-rank-approximation/TR-07/problem.tex)


<a id="tr-08"></a>

## TR-08 — Sharp sparsity threshold for injectivity of a random sparse rectangular matrix

[Open the problem folder](../../randomized-and-low-rank-approximation/TR-08/README.md) · [PDF](../../randomized-and-low-rank-approximation/TR-08/problem.pdf) · [LaTeX](../../randomized-and-low-rank-approximation/TR-08/problem.tex)


<a id="tr-09"></a>

## TR-09 — Subquadratic overparameterization for iterative decomposition of smoothed tensors

[Open the problem folder](../../tensor-computations/TR-09/README.md) · [PDF](../../tensor-computations/TR-09/problem.pdf) · [LaTeX](../../tensor-computations/TR-09/problem.tex)


## Screened items that are not counted

These are exclusions, not additional open problems. Reports of a new proof or counterexample are sufficient to suspend admission; their presence here does not represent independent verification of every proof.

| Candidate | Reason for exclusion and source |
|---|---|
| Nelson–Nguyen optimal SparseStack OSE conjecture | A claimed full proof appeared on **2026-09-02**: Diar Heidary, [*SparseStack Is an Optimal Oblivious Subspace Embedding*](https://arxiv.org/abs/2609.02978). It must not remain on an open list merely because the April workshop version calls it open. |
| Constant-sparsity SparseStack injectivity | Huang, Rudelson, and Tikhomirov, [July 2026 preprint](https://arxiv.org/html/2607.05384v2), Corollary 1.6, gives a negative answer to workshop Problem 5.5. Its fresh §7 questions are TR-07 and TR-08. |
| Polynomial conditioning guarantee for QRCP on a matrix with orthonormal rows | [*Iteris: Agentic Research Loops for Computational Mathematics*](https://arxiv.org/html/2606.02484v1), §4.3 and Appendix 7, reports counterexamples to workshop Problem 4.3, including bounded-coherence families. |
| Nyström diminishing-returns question for SDDM/SDD inverses | Matthew J. Colbrook, [*Nyström Error Beyond M-Matrices: A Minimal Diagonally Dominant Obstruction*](https://arxiv.org/abs/2607.19282), July 2026, settles the SDDM case positively and gives an order-three SDD counterexample. The abstract explicitly identifies workshop Problem 4.6 as answered. |
| Constant-failure-probability OSI sketch-and-solve | Alex Townsend and Chris Wang, [*Oblivious Subspace Injection Is Not Enough for Relative Error*, v2](https://arxiv.org/abs/2604.10215v2), August 2026, §3.1, gives a counterexample to relative error controlled solely by the OSI failure parameter (workshop Problem 5.1). |
| OSI randomized-SVD claim as printed | Townsend and Wang, [same paper, v2](https://arxiv.org/abs/2604.10215v2), §4.1, gives a randomized-SVD counterexample to OSI-only relative error (workshop Problem 5.2). It is excluded on this substantive status evidence. |
| Hamiltonian-derived NEPv identity as printed | Sra, [August 2026 manuscript](https://arxiv.org/html/2608.29595v1), Appendix A.5, identifies a same-site-term obstruction to the displayed identity in workshop §6.2. The defective formulation is not an open problem. |

The searches establish a documented literature check, not exhaustive coverage of every book, publication, or unindexed result through the check date.

- **Reserved ID TR-02: GECP for the continuous fermionic kernel.** The
  [August workshop revision](https://arxiv.org/html/2602.05394v3), update after
  Problem 4.2, records a full solution claim by V. S. Pendyala,
  [*Local-to-Global Convergence of Greedy Cross Approximation for Totally
  Positive Kernels*](https://doi.org/10.5281/zenodo.21863274) (2026).
  It claims exactly the logarithmic cutoff/accuracy rate considered in the
  earlier draft. This entry is excluded; the catalog does not certify the
  proof. Related work is M. A. Gilles,
  [*Convergence rates for pivoted QR and LU*](https://arxiv.org/abs/2607.26863).
  The v3 check on 2026-09-08 supersedes the unsuccessful title searches based
  on the April workshop version.
