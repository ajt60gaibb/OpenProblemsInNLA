# Tensors, low-rank approximation, and randomized linear algebra

This file contains **8 admitted problems**. Labels are editorial assessments, not ratings supplied by the cited authors. “Open” means an explicit published question or conjecture was located and a search for subsequent resolutions found none that covers the stated assumptions. It does not certify that no resolution exists. All status searches below were performed on **2026-09-08**; the dates of the underlying evidence are recorded separately.

<a id="tr-01"></a>

## TR-01 — Optimal dimension for a rerandomized Hadamard embedding

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open; explicit source updated 2026-08-20.

Let $n$ be a power of two, $1\le r\le n$, and $0<\varepsilon<1/2$. Let $F$ be the normalized Walsh–Hadamard matrix, let $D_1,D_2$ have independent Rademacher diagonal entries, and let $S\in\mathbb R^{n\times k}$ select a uniformly random $k$-element subset of coordinates, independently. Set

$$
\Omega=\sqrt{n/k}\,D_1FD_2FS.
$$

Does a universal $C>0$ exist such that, for every fixed $r$-dimensional subspace $V\subseteq\mathbb R^n$, choosing $k=\min\{n,\lceil Cr/\varepsilon^2\rceil\}$ gives

$$
\Pr\left\{(1-\varepsilon)\|x\|_2^2\le
\|\Omega^Tx\|_2^2\le(1+\varepsilon)\|x\|_2^2
\text{ for every }x\in V\right\}\ge0.99?
$$

This fixes normalization, sampling without replacement, and a constant success probability in the workshop question. Results for a single randomization, three randomizations, or independently sampled sparse sketches do not establish this statement.

**References.** Amsel et al., [*Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop*](https://arxiv.org/html/2602.05394v3), §5.3, Definition 5.3 and Problem 5.6. For the single-round baseline, Joel A. Tropp, [*Improved Analysis of the Subsampled Randomized Hadamard Transform*](https://arxiv.org/abs/1011.1595), *Advances in Adaptive Data Analysis* 3 (2011), 115–126, Theorem 3.1.

**Status check.** Searches included `"rerandomized SRHT" counterexample`, `"rerandomized" "subspace" Hadamard`, and `"Hadamard" "two" "2026" embedding conjecture`. No resolution of the displayed two-round assertion was located. The September 2026 SparseStack result listed below concerns another distribution.

<a id="tr-03"></a>

## TR-03 — Sharp gap between volume sampling and the worst matrix with a prescribed spectrum

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open quantitative subquestion of a source updated 2026-08-20.

For $n\ge3$, $1\le k\le n-2$, and $\lambda\in(0,\infty)^n$, write $K_V=V^T\operatorname{diag}(\lambda)V$, $V\in O(n)$, and define

$$
x_k(\lambda)=\max_{V\in O(n)}\min_{|I|=k}
\operatorname{tr}\bigl(K_V-(K_V)_{:I}(K_V)_{II}^{-1}(K_V)_{I:}\bigr),
\quad
y_k(\lambda)=(k+1)\frac{e_{k+1}(\lambda)}{e_k(\lambda)},
$$

where $e_j(\lambda)=\sum_{|I|=j}\prod_{i\in I}\lambda_i$. Determine, up to universal multiplicative constants, the dependence on $n,k$ of

$$
R_{n,k}=\sup_{\lambda\in(0,\infty)^n}\frac{y_k(\lambda)}{x_k(\lambda)}.
$$

Here $y_k$ is the expected trace error when the selected subset has probability $\det((K_V)_{II})/e_k(\lambda)$. The question compares that expectation with optimal subset selection after an adversary chooses the eigenvectors. This order of quantifiers is essential. The endpoint $R_{n,n-1}=1$ is known and excluded. The displayed supremum is a concrete subquestion of the source’s request for spectrum-dependent tightness bounds; stronger bounds retaining the full spectrum would also be valuable.

**References.** Amsel et al., [workshop report](https://arxiv.org/html/2602.05394v3), §4.2, Problem 4.7 and equations (15)–(16). Mark Fornace and Michael Lindsey, [*Column and Row Subset Selection Using Nuclear Scores: Algorithms and Theory for Nyström Approximation, CUR Decomposition, and Graph Laplacian Reduction*](https://arxiv.org/html/2407.01698v2), §4 and Appendix C, for determinantal sampling and the elementary-symmetric-polynomial formulas.

**Status check.** Searches included `"minimax" "volume sampling" "2026"`, `"volume sampling" "worst" "spectrum" "2026"`, and `"volume sampling" "tightness" Fornace`. No matching sharp estimate for $R_{n,k}$ was located. Generic column-subset approximation guarantees do not by themselves settle this spectral minimax ratio.

<a id="tr-04"></a>

## TR-04 — Improve the worst-case approximation factor for prescribed tensor-train ranks

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** open; explicit source updated 2026-08-20.

Let $d\ge3$, $n_1,\ldots,n_d\ge2$, and positive integers $r_1,\ldots,r_{d-1}$ be given. Let $S_r\subset\mathbb R^{n_1\times\cdots\times n_d}$ consist of tensors whose unfolding separating modes $1,\ldots,j$ from modes $j+1,\ldots,d$ has rank at most $r_j$, for every $j$. For a dense input tensor $A$, put

$$
E_*(A,r)=\min_{Y\in S_r}\|A-Y\|_F^2.
$$

Find a polynomial-time algorithm returning $X\in S_r$ with

$$
\|A-X\|_F^2<(d-1)E_*(A,r)
\qquad\text{whenever }E_*(A,r)>0,
$$

and exact reconstruction when $E_*(A,r)=0$; alternatively, establish a complexity obstruction to such a guarantee. Ranks may not be increased. Polynomial time is measured in the dense input size and rank parameters, in the idealized arithmetic/SVD model used for TT-SVD; a bit-complexity formulation must additionally specify precision and output tolerances.

This is the tensor-train case of the published tree-network question. The positive-error qualification corrects the impossible strict inequality at zero optimum. It asks for a uniformly valid algorithm, not an empirical improvement or a guarantee restricted to particular input tensors.

**References.** I. V. Oseledets, [*Tensor-Train Decomposition*](https://doi.org/10.1137/090752286), *SIAM Journal on Scientific Computing* 33 (2011), 2295–2317, Theorem 2.2 and Corollary 2.4. Amsel et al., [workshop report](https://arxiv.org/html/2602.05394v3), §6.1, Problem 6.1. Matthew Fahrbach and Mehrdad Ghadiri, [*A Tight Lower Bound for the Approximation Guarantee of Higher-Order Singular Value Decomposition*](https://arxiv.org/html/2508.06693v1), Theorems 1.2–1.3, concerns tightness of specific Tucker algorithms rather than a lower bound against all tensor-train algorithms.

**Status check.** Searches included `"tensor train" "approximation" "2026" "improvement"` and `"tree tensor" "approximation guarantee" "2026"`. No universal improvement or matching complexity lower bound was located. Randomized methods and better practical error estimates require a separate comparison with the displayed worst-case statement.

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

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open conjecture; explicit journal source published in 2023.

Under the shared model, prove or disprove

$$
\mathbb E_\mu\kappa(A)=\infty
$$

for every admissible format and $r\ge2$. Rank two is already proved. The unresolved task removes the additional smaller-format identifiability assumption used for the higher-rank theorem; it must not be counted again for parameter ranges covered by that theorem.

**Reference.** Carlos Beltrán, Paul Breiding, and Nick Vannieuwenhoven, [*The Average Condition Number of Most Tensor Rank Decomposition Problems Is Infinite*](https://doi.org/10.1007/s10208-022-09551-1), *Foundations of Computational Mathematics* 23 (2023), 433–491: Definition 1, Assumption 1, equation (5), Theorems 1–2, and Conjecture 1. The [author preprint](https://arxiv.org/pdf/1903.05527) labels the conjecture 1.8.

**Status check.** Searches included `"average condition number" "tensor" conjecture 2025 2026` and `"regular condition number" "tensor" "2026" conjecture proof`. No removal of the remaining hypothesis was located. The latest explicit conjecture located is the 2023 journal version.

<a id="tr-06"></a>

## TR-06 — Finite mean angular condition number for identifiable tensor decomposition

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** open conjecture; explicit journal source published in 2023.

Under the shared model, prove or disprove

$$
\mathbb E_\mu\kappa_{\rm ang}(A)<\infty
$$

for every admissible format and $r\ge3$. The rank-two case is a theorem. Normalizing each recovered summand inside the derivative is part of the definition; simply dividing the regular condition number by a scalar does not give this problem.

**Reference.** Beltrán, Breiding, and Vannieuwenhoven, [*The Average Condition Number of Most Tensor Rank Decomposition Problems Is Infinite*](https://doi.org/10.1007/s10208-022-09551-1), *Foundations of Computational Mathematics* 23 (2023), 433–491: equation (6), Theorem 3, and Conjecture 2. The [author preprint](https://arxiv.org/pdf/1903.05527) labels the conjecture 1.10.

**Status check.** Searches included `"tensor" "angular condition number" "2026"` and `"angular condition" "tensor" finite proved`. No higher-rank resolution was located. Generic uniqueness alone is not an integrability estimate. The latest explicit conjecture located is the 2023 journal version.

<a id="tr-07"></a>

## TR-07 — Random column subsets of arbitrary fixed-sparsity matrices

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open conjecture in a preprint updated 2026-07-08.

Fix an integer $s\ge2$ and $C\ge1$. Suppose $r_k\le k$, $k/r_k\to C$, and $n_k/r_k\to\infty$. For every deterministic sequence $M_k\in\{-1,0,1\}^{k\times n_k}$ with exactly $s$ nonzero entries per column, and a uniformly random $r_k$-element column set $I_k$, prove or disprove

$$
\forall\eta>0,\qquad
\Pr\{\sigma_{\min}((M_k)_{:I_k})>\eta\}\longrightarrow0.
$$

Here $\sigma_{\min}(B)=\inf_{\|x\|_2=1}\|Bx\|_2$. There is no hypothesis controlling intersections of column supports.

**Reference.** Han Huang, Mark Rudelson, and Konstantin Tikhomirov, [*Well-Invertible Column Subsets of Sparse Matrices Are Rare*](https://arxiv.org/html/2607.05384v2), §7, Conjecture 7.1; compare Theorem 1.3 for the additional structural hypothesis in the proved result.

**Status check.** Searches included `"unrestricted deterministic sparse sketches" conjecture` and the exact paper title with `2026`. No subsequent resolution was located. The paper’s disproof of a particular SparseStack conjecture does not establish its own unrestricted deterministic conjecture.

<a id="tr-08"></a>

## TR-08 — Sharp sparsity threshold for injectivity of a random sparse rectangular matrix

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open problem in a preprint updated 2026-07-08.

Let $k\to\infty$ through multiples of 100, $n_k\ge k^{1+c}$ for fixed $c>0$, and $1\le s_k\le k$. Independently for each column of $M_k\in\mathbb R^{k\times n_k}$, choose $s_k$ distinct row locations uniformly and put independent signs $\pm1/\sqrt{s_k}$ there. Independently select a uniform $k/100$-element column set $I_k$.

Determine necessary and sufficient asymptotic conditions on $s_k$ for the existence of an absolute $a>0$ such that

$$
\Pr\{\sigma_{\min}((M_k)_{:I_k})\ge a\}=1-o(1).
$$

Probability includes both random constructions. The requested threshold concerns a lower singular-value bound, not an upper distortion estimate.

**Reference.** Huang, Rudelson, and Tikhomirov, [*Well-Invertible Column Subsets of Sparse Matrices Are Rare*](https://arxiv.org/html/2607.05384v2), §7, Problem 7.2.

**Status check.** Searches included `"Optimal OSI sparsity" "2026"` and the paper title with `threshold`. No sharp threshold result was located. A sufficient condition from a two-sided embedding theorem would not on its own establish necessity here.

<a id="tr-09"></a>

## TR-09 — Subquadratic overparameterization for iterative decomposition of smoothed tensors

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** open; source published in 2026, with expressly partial progress in August 2026.

Given $n\ge r$, take arbitrary base factors $\bar A,\bar B,\bar C\in\mathbb R^{n\times r}$, and form $A,B,C$ by adding independent Gaussian entries of variance $\rho^2/n$, where $\rho=r^{-q}$ and $q>0$ is fixed. The input is

$$
T=\sum_{j=1}^{r}a_j\otimes b_j\otimes c_j.
$$

Does there exist $k(r)=o(r^2)$, a polynomial lower bound $n_0(r)$, and an explicitly specified ALS or gradient-descent method, initialized randomly, such that for every $n\ge n_0(r)$ and $0<\varepsilon<1$ it returns $k$ summands with

$$
\left\|T-\sum_{i=1}^{k}x_i\otimes y_i\otimes z_i\right\|_F
\le\varepsilon\|T\|_F
$$

using polynomially many exact real arithmetic operations in $n,r,\log(1/\varepsilon)$, with probability $1-o_r(1)$ over the once-drawn smoothed input and at least inverse-polynomial conditional success over initialization? Update rules, initialization, and permitted restarts must be specified. Initial factors must be sampled independently of the input and its unknown factors, apart from an explicitly specified scalar scale normalization and dependence on $n,r,\rho,\varepsilon$. The method must optimize the squared residual by alternating block least squares or gradient steps; substituting an algebraic tensor-recovery algorithm does not answer the question. The base-factor quantifier must be preserved rather than replaced by assumptions about the successful trajectory.

**References.** Dionysis Arvanitakis, Vaidehi Srinivas, and Aravindan Vijayaraghavan, [*Open Problem: How Much Overparametrization Is Needed for ALS in Tensor Decomposition?*](https://proceedings.mlr.press/v336/arvanitakis26a.html), COLT 2026, PMLR 336, 7105–7110, §2, Open Problem 2 and the following probability clarification. Zhang et al., [*VALG: An Agentic System for ML Theory Research and Demonstrations on COLT 2026 Open Problems*](https://arxiv.org/html/2608.13060v1), §4.1.1, Theorem 4.1 and Discussion.

**Status check.** Searches included `"ALS" "subquadratic" tensor 2026` and the exact COLT problem title. VALG reports $k=\Theta(r^{5/3}(\log r)^{5/2})$ under additional scale, interference, balance, smoothing, and dimension assumptions, and explicitly calls the result partial. That result does not resolve the general base-factor formulation. The source informally motivates well-conditioned factors but its displayed smoothed model permits arbitrary base factors; this entry follows that displayed quantifier. A future revision may distinguish a uniformly norm-bounded base model once a precise source formulation is identified.

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
| Hamiltonian-derived NEPv identity as printed | Sra, [same paper](https://arxiv.org/html/2608.29595v1), Appendix A.5, identifies a same-site-term obstruction to the displayed identity in workshop §6.2. The defective formulation is not an open problem. |

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
