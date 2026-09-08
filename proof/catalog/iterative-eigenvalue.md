# Iterative methods, eigenvalue computation, and elimination

Status checks below were performed on **2026-09-08**. “No resolution found” means that the cited later papers and the recorded searches did not identify one; it is not a proof that no unpublished solution exists. Difficulty and importance are editorial judgments. Entries are individual mathematical questions, not dimension-by-dimension expansions of a general question.

## Conventions for elimination problems

All elimination in these statements is in exact arithmetic. Write $\|A\|_{\max}=\max_{ij}|a_{ij}|$. A pivoting path creates successive active Schur complements $S_1=A,S_2,\ldots,S_n$, with row/column permutations as appropriate. Its element-growth factor is

$$
\rho(A)=\frac{\max_{1\leq j\leq n}\|S_j\|_{\max}}{\|A\|_{\max}}.
$$

Partial pivoting chooses a largest-magnitude entry in the active first column; complete pivoting chooses one anywhere in the active matrix. If ties occur, a universal statement includes every admissible tie choice; a supremum includes all admissible paths. These conventions remove implementation-dependent ambiguity. Matrices are nonsingular unless otherwise stated.

<a id="ie-01"></a>

## IE-01 — Forsythe's conjecture beyond restart length two

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** open; the case of restart length two has a recent proof claim.

Let $A\in\mathbb R^{n\times n}$ be symmetric positive definite, $b,x_0\in\mathbb R^n$, and $3\leq s<n$. At each restart, perform exactly $s$ exact-arithmetic conjugate-gradient steps, starting from the last iterate, and discard the previous search directions. Denote the iterate after restart cycle $j$ by $x_j$. Suppose this process never terminates exactly, and put

$$
r_j=b-Ax_j,\qquad y_j=r_j/\|r_j\|_2.
$$

Prove or disprove that both $(y_{2j})_{j\geq0}$ and $(y_{2j+1})_{j\geq0}$ converge in $\mathbb R^n$, for every such input and restart length. The question concerns directions, not whether the residual norms tend to zero. Exact termination is excluded so every normalization exists.

**References:** Faber, Liesen, and Tichý, [*On the Forsythe conjecture*](https://doi.org/10.1007/s10543-023-00991-x), BIT 63 (2023), §2, especially the displayed Forsythe conjecture. Colbrook, Stepaniants, and Townsend, [*A Proof of the Forsythe Conjecture for the Two-Step Restarted Conjugate Gradient Method*](https://arxiv.org/abs/2608.02852), August 2026, §1 and main theorem.

**Status check:** Searches for `Forsythe conjecture 2026 proof` found the August preprint. Its claimed theorem covers $s=2$, not all $s\geq3$. The surviving range is therefore stated explicitly; older claims that every $s\geq2$ remains open are obsolete.

<a id="ie-02"></a>

## IE-02 — Is the ideal GMRES bound sharp for every Jordan block?

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** open; several parameter regimes are known.

For $n\geq2$ and $\lambda\in\mathbb C\setminus\{0\}$, let $J_n(\lambda)=\lambda I+N$, where $N_{i,i+1}=1$ and all other entries of $N$ vanish. Let $\mathcal P_k=\{p\in\mathbb C[z]:\deg p\leq k,\ p(0)=1\}$. Define

$$
\psi_k(J)=\max_{\|v\|_2=1}\min_{p\in\mathcal P_k}\|p(J)v\|_2,
\qquad
\phi_k(J)=\min_{p\in\mathcal P_k}\|p(J)\|_2.
$$

Prove or disprove $\psi_k(J_n(\lambda))=\phi_k(J_n(\lambda))$ for every $1\leq k<n$. The maximum describes the slowest possible GMRES residual reduction, whereas the minimum over operator norms is the ideal bound. The familiar inequality $\psi_k\leq\phi_k$ does not answer the question. A single Jordan block is a published structural test case, not a claim about all nonnormal matrices.

**References:** Tichý, Liesen, and Faber, [*On worst-case GMRES, ideal GMRES, and the polynomial numerical hull of a Jordan block*](https://etna.ricam.oeaw.ac.at/volumes/2001-2010/vol26/abstract.php?pages=453-473), ETNA 26 (2007), 453–473, §1 conjecture and subsequent special cases. Faber, Liesen, and Tichý, [*Matrix best approximation in the spectral norm*](https://arxiv.org/abs/2506.09687), published in LAA 733 (2026), §§4–5.

**Status check:** Searches for `Jordan block ideal GMRES equality proved 2026` and `site:arxiv.org GMRES Jordan block` found the original partial results and the 2026 general approximation paper, but no resolution of the displayed Jordan-block equality. The latter paper's doubling theorem changes the matrix and does not by itself establish this statement.

<a id="ie-03"></a>

## IE-03 — Cryer's Hadamard complete-pivoting conjecture

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** open.

A real Hadamard matrix of order $n$ is a matrix $H\in\{-1,1\}^{n\times n}$ satisfying $HH^T=nI$. Prove or disprove that, for every Hadamard matrix and every complete-pivoting path,

$$
\rho(H)=n.
$$

The quantified input is an existing Hadamard matrix; this question does not ask whether Hadamard matrices exist in every order divisible by four. Since $\|H\|_{\max}=1$, the requested upper bound says that no entry in any active Schur complement can exceed $n$ in absolute value. The final pivot already supplies the matching lower bound. Permuting or resigning rows and columns does not remove the need to account for all allowed pivot paths.

**References:** N. J. Higham, [*Accuracy and Stability of Numerical Algorithms*,
2nd ed.](https://doi.org/10.1137/1.9780898718027), SIAM (2002), Problem 9.17,
p. 193, poses this book-sourced question. Kravvaritis and Mitrouli, [*The growth factor of a Hadamard matrix of order 16 is 16*](https://doi.org/10.1002/nla.637), NLA with Applications 16 (2009), 715–743, introduction and main result. Peca-Medlin, [*Complete pivoting growth of butterfly matrices and butterfly Hadamard matrices*](https://doi.org/10.1080/03081087.2026.2660796), 2026, introduction and §2.

**Status check:** Searches for `Hadamard Cryer 2026` and `Hadamard growth conjecture 2026 proof` found the general conjecture still identified as open in the 2026 butterfly paper. Shah–Urschel's August 2026 general elimination construction is not a Hadamard counterexample. Known Sylvester and small-order cases must not be counted as additional open problems.

<a id="ie-04"></a>

## IE-04 — Exponential smoothed tail bounds for partial pivoting

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** open.

Do universal constants $c_1,c_2>0$ exist such that, for every $n\geq1$, deterministic $\bar A\in\mathbb R^{n\times n}$ with $\|\bar A\|_2\leq1$, $0<\sigma\leq1$, and $x\geq1$, the matrix $A=\bar A+\sigma G$, with independent standard normal entries in $G$, satisfies

$$
\Pr\!\left\{\rho_{\mathrm{PP}}(A)>x(n/\sigma)^{c_1}\right\}
\leq 2^{-c_2x}?
$$

This is a uniform smoothed-analysis question: the deterministic center may itself be a worst-case input. Almost surely the perturbed matrix is nonsingular and the pivot choices have no ties. Numerical evidence or estimates only at $\bar A=0$ do not settle the quantifier over deterministic centers. The tail estimate would quantify the rarity of substantial growth after small Gaussian input perturbations.

**References:** Spielman and Teng, [*Smoothed Analysis: An Attempt to Explain the Behavior of Algorithms in Practice*](https://www.cs.yale.edu/homes/spielman/PAPERS/focmSmoothed.pdf), §P6, Conjecture 16, p. 52 of the author PDF. Huang and Tikhomirov, [*Average-case analysis of the Gaussian elimination with partial pivoting*](https://doi.org/10.1007/s00440-024-01276-2), PTRF 189 (2024), introduction.

**Status check:** Searches for `Exponential Stability of GEPP solved` and `Gaussian elimination smoothed analysis 2025 2026` found the average-case theorem, not this exponential tail bound. The 2026 Peca-Medlin butterfly paper also distinguishes average-case results from the still-unavailable full smoothed analysis. Randomizing the pivot rule is a different model.

<a id="ie-05"></a>

## IE-05 — Exact extremizers for partial pivoting on orthogonal matrices

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** open.

Let $L_n$ be the real unit lower triangular matrix whose entries strictly below the diagonal are all $-1$. Define $Q_n$ by the unique QR factorization $L_n=Q_nR_n$ with positive diagonal in $R_n$. For $Q_n$, use partial pivoting with the first available row chosen in a tie. Is it true that, for every $n\geq2$,

$$
\sup_{Q\in O(n)}\rho_{\mathrm{PP}}(Q)
=\rho_{\mathrm{PP}}(Q_n),
\qquad O(n)=\{Q\in\mathbb R^{n\times n}:Q^TQ=I\}?
$$

The supremum on the left includes all admissible partial-pivoting paths. The candidate is fully specified by $L_n$, rather than by an approximate numerical optimizer. This asks for the sharp extremizer, beyond the established exponential order of orthogonal growth.

**Reference:** Peca-Medlin, [*Growth factors of orthogonal matrices and local behavior of Gaussian elimination with partial and complete pivoting*](https://arxiv.org/html/2308.16146v2), published in SIAM J. Matrix Anal. Appl. (2024), §3.2 and Appendix B. The paper conjectures this equality and establishes $\rho_{\mathrm{PP}}(Q_n)=2^{n-1}(1+o(1))/\sqrt3$.

**Status check:** Searches for `GEPP orthogonal conjecture 2026` and the exact paper title found no proof of the extremal equality. The 2026 butterfly paper still identifies orthogonal partial-pivoting growth as open. The August Shah–Urschel results concern different growth questions and pivot strategies; their exponential examples do not establish this exact supremum.

<a id="ie-06"></a>

## IE-06 — The square-root upper bound for Gaussian partial-pivoting growth

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open; polynomial growth with high probability is known.

Let $G_n\in\mathbb R^{n\times n}$ have independent $N(0,1)$ entries. Is the following precise square-root upper-bound conjecture true?

$$
\text{For every }\eta>0,\qquad
\lim_{n\to\infty}\Pr\{\rho_{\mathrm{PP}}(G_n)>n^{1/2+\eta}\}=0.
$$

Here growth is measured over the exact-arithmetic Schur complements as defined above. This formulation asks only for the conjectured upper exponent; it does not add an unsupported matching lower-bound assertion or a limiting-distribution claim. It is also distinct from IE-04, which requires a uniform result after perturbing every deterministic center and prescribes an exponential tail.

**References:** Huang and Tikhomirov, [*Average-case analysis of the Gaussian elimination with partial pivoting*](https://doi.org/10.1007/s00440-024-01276-2), PTRF 189 (2024), 501–567, introduction, discussion of Edelman's numerical evidence and main theorems. Trefethen and Schreiber, [*Average-Case Stability of Gaussian Elimination*](https://doi.org/10.1137/0611023), SIAM J. Matrix Anal. Appl. 11 (1990), 335–360.

**Status check:** Searches for `Gaussian elimination n^{1/2} 2025 2026` and `site:arxiv.org Gaussian growth factor 2026` found polynomial upper bounds and the August worst-case results, but no proof at the square-root exponent. The distinction between exact and computed growth factors matters; the catalog statement fixes the former.

<a id="ie-07"></a>

## IE-07 — Deterministic regularization of the nonsymmetric eigenproblem

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** open.

For a matrix $M$ with simple spectrum, define

$$
\operatorname{gap}(M)=\min_{i\ne j}|\lambda_i(M)-\lambda_j(M)|,
\qquad
\kappa_V(M)=\inf_{M=VDV^{-1},\ D\text{ diagonal}}\|V\|_2\|V^{-1}\|_2.
$$

For every $n\geq2$, $A\in\mathbb C^{n\times n}$ with $\|A\|_2\leq1$, and $0<\delta<1/2$, construct deterministically a matrix $E$ such that

$$
\|E\|_2\leq\delta,\qquad A+E\text{ has simple spectrum},\qquad
\frac{\kappa_V(A+E)}{\operatorname{gap}(A+E)}\leq C(n/\delta)^c,
$$

using $O(n^3\log^d(n/\delta))$ exact arithmetic operations, for universal constants $C,c,d$. The task is to find the perturbation, not merely prove its existence.

**References:** Banks, Garza-Vargas, Kulkarni, and Srivastava, [*Pseudospectral Shattering, the Sign Function, and Diagonalization in Nearly Matrix Multiplication Time*](https://doi.org/10.1007/s10208-022-09577-5), FOCM 23 (2023), §6, first future-research question. Amsel et al., [*Linear Systems and Eigenvalue Problems*](https://arxiv.org/html/2602.05394v3#S3.SS1), August 2026, Problem 3.1.

**Status check:** Searches for `deterministic pseudospectral shattering 2026` found randomized and exponential-bound deterministic results, not the stated algorithm. The normalization and exponent orientation here are explicit: Problem 3.1's printed $(\delta/n)^c$ contradicts its own preceding motivation; $(n/\delta)^c$ is the intended polynomial upper bound.

<a id="ie-08"></a>

## IE-08 — A cubic-time Schur algorithm using logarithmic precision

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** open.

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

**References:** Amsel et al., [*Linear Systems and Eigenvalue Problems*](https://arxiv.org/html/2602.05394v3#S3.SS2), Problem 3.3. Schneider, [*Pseudospectral Divide-and-Conquer for the Generalized Eigenvalue Problem*](https://escholarship.org/content/qt3bb8s95w/qt3bb8s95w_noSplash_22c8cf7d2873d111b5bb367d09dc40fc.pdf), dissertation, §1.6.1 and Chapter 6. Banks et al., [FOCM diagonalization paper](https://doi.org/10.1007/s10208-022-09577-5), §6, precision-reduction question.

**Status check:** Searches for `Schur logarithmic precision 2026` and `site:arxiv.org Schur precision 2026` found no complete analysis meeting both bounds. The dissertation explicitly distinguishes analyzed subroutines from an end-to-end precision theorem.

<a id="ie-10"></a>

## IE-10 — Conditioning of a random Krylov compression of a cyclic shift

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** open.

Let $C_n\in\mathbb C^{n\times n}$ be the cyclic shift, $C_ne_j=e_{j+1}$ for $j<n$ and $C_ne_n=e_1$. Draw $b$ uniformly from the complex unit sphere. For $2\leq k<n$, let $Q$ have orthonormal columns spanning

$$
\mathcal K_k(C_n,b)=\operatorname{span}\{b,C_nb,\ldots,C_n^{k-1}b\},
\qquad H=Q^*C_nQ.
$$

This subspace has dimension $k$ almost surely. Define $\kappa_V(H)$ as in IE-07, and set it to $+\infty$ if $H$ is not diagonalizable. Do universal constants $C,c>0$ exist such that, for every $n\geq3$ and $2\leq k<n$, with the same constants,

$$
\Pr\{\kappa_V(H)\leq Cn^c\}\geq0.99?
$$

Changing the orthonormal basis of the same Krylov space does not affect this question. Randomness belongs to the starting vector; replacing $Q$ by an independently Haar-distributed subspace would change the model.

**Reference:** Amsel et al., [*Linear Systems and Eigenvalue Problems*](https://arxiv.org/html/2602.05394v3#S3.SS3), Problem 3.5, which explicitly singles out the circulant shift. This entry fixes “high probability” to a uniform 0.99 success target.

**Status check:** Searches for `Krylov circulant shift condition 2026` and `random Krylov compression eigenvector condition number` found no solution. The deterministic starting vector $e_1$ gives a Jordan compression, so the unrandomized statement would be false; that exceptional example does not settle the probabilistic problem. The workshop report’s 20 August update reports [Peng’s obstruction](https://yangpliu.github.io/repository.html) for arbitrary real diagonalizable inputs with ill-conditioned eigenvectors and real Gaussian starts. It explicitly leaves the normal-input case open, which includes the cyclic shift here.

<a id="ie-11"></a>

## IE-11 — The exact fifth complete-pivoting growth factor

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** open.

Let

$$
g_5=\sup\{\rho_{\mathrm{CP}}(A):A\in\mathbb R^{5\times5}\text{ nonsingular}\}.
$$

Let $\alpha$ be the unique real root in $(4,5)$ of the integer polynomial $P_5$ displayed in Equation (2.15) of the primary reference below. This definition specifies an exact algebraic number; numerically $\alpha\approx4.1325170786324728542$. Prove or disprove

$$
g_5=\alpha.
$$

All complete-pivoting paths are included in the supremum. The lower bound $g_5\geq\alpha$ is already established in the cited paper. The unresolved part is global optimality over all allowable patterns of active constraints, not exact evaluation of a particular numerical example. Order five is independently singled out by the literature as the first unresolved dimension; this catalog does not split the same question into entries for every subsequent order.

**Reference:** Chen, Edelman, and Urschel, [*The largest 5th pivot may be the root of a 61st degree polynomial*](https://arxiv.org/html/2602.20390v1), February 2026, Equation (2.15), Conjecture 2.1, Theorem 2.2, and Theorem 3.5. The current rigorous interval is $\alpha\leq g_5\leq4.84$.

**Status check:** Searches for the paper title and `complete pivoting maximum five 2026` found no global proof. Shah–Urschel's August asymptotic result leaves this exact finite-dimensional optimum undetermined.

<a id="ie-12"></a>

## IE-12 — Near-quadratic solution cost at a prescribed backward error

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** open; removing dimension-dependent overhead from general backward-error solution cost.

Does there exist a randomized algorithm and absolute constants $C,q>0$ such
that, for every $n\ge1$, nonsingular $A\in\mathbb R^{n\times n}$ with
$\|A\|_2=1$, $b\ne0$, and $0<\varepsilon<1/2$, it returns $x\ne0$ satisfying

$$
\Pr\left\{\frac{\|Ax-b\|_2}{\|A\|_2\|x\|_2}
\le\varepsilon\right\}\ge0.99
$$

using at most $C n^2\varepsilon^{-q}$ operations? Use an exact-real arithmetic
model with scalar arithmetic, square roots, comparisons, and independent
standard Gaussian or random-bit draws at unit cost. All input entries may be
accessed; the norm normalization is an input promise. The cost constants must
be independent of the condition number and of $n,b,\varepsilon$.
The fraction is normwise backward error with perturbations allowed in $A$
only. A deterministic algorithm meeting the bound would also answer positively.

**References and status.** M. Dereziński, Y. Nakatsukasa, and E. Rebrova,
[*Towards Universal Convergence of Backward Error in Linear System Solvers*](https://arxiv.org/html/2604.16075v2)
(22 May 2026), §§1, 3.1, 5.2, 7, poses the cost question and specifies the
backward-error metric. Corollary 17 gives $O(n^2/\sqrt\varepsilon)$ for PSD
systems. The revised paper's Corollary 25 proves the general-system bound
$O(n^2\log(n/\delta)/\varepsilon)$ with failure probability $\delta$;
its §7 asks for convergence independent of dimension. The remaining target
here removes the $\log n$ overhead, which cannot be hidden in a constant
depending only on $\varepsilon$. The model and success probability above
make this explicit. Searches on 2026-09-08 for “universal backward error 2026
linear systems”, “MINBERR smoothed analysis”, and “quadratic backward error
linear solver” found no resolution of the displayed bound. The earlier
version's lack of a proved general-system rate is no longer current.

## Uncounted candidate IE-09 — Stable selected bidiagonal singular vectors

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** withheld; ID reserved. A source-faithful, nonvacuous precision/cost model needs further work. The provisional formulation below is not an admitted open problem.

Let $B\in\mathbb R^{n\times n}$ be upper bidiagonal, let $1\leq\ell\leq r\leq n$, and put $k=r-\ell+1$. At a fixed working precision with unit roundoff $u$, construct a floating-point algorithm using $O(nk)$ operations that returns the selected singular values and associated approximately normalized vectors $(\widehat\sigma_i,u_i,v_i)$, $\ell\leq i\leq r$, with

$$
|\widehat\sigma_i-\sigma_i(B)|\leq Cnu\|B\|_2,
\quad
\max\{\|Bv_i-\widehat\sigma_i u_i\|_2,
\|B^Tu_i-\widehat\sigma_i v_i\|_2\}\leq Cnu\|B\|_2,
$$
$$
\max\{|u_i^Tu_j|,|v_i^Tv_j|\}\leq Cnu\quad(i\ne j),
$$

for a universal $C$, all $nu$ sufficiently small, and all inputs including clustered and zero singular values. The intended cost must have a specified uniform dependence on precision; allowing an arbitrary constant depending on fixed $u$ makes the complexity target vacuous when $nu$ is restricted. Vector normalization should likewise mean $|\|u_i\|_2^2-1|,|\|v_i\|_2^2-1|\leq Cnu$, rather than exact normalization of floating-point outputs. Singular values are indexed in descending order, and overflow and underflow are excluded.

**References:** Großer and Lang, [*The bidiagonal MRRR algorithm*](https://www.netlib.org/lapack/lawnspdf/lawn166.pdf), §4. Marques, Demmel, and Vasconcelos, [*Bidiagonal SVD Computation via an Associated Tridiagonal Eigenproblem*](https://icl.utk.edu/files/publications/2018/icl-utk-1040-2018.pdf), introduction and discussion of clusters. Amsel et al., [2026 survey](https://arxiv.org/html/2602.05394v3#S3.SS4), Problem 3.8.

**Status check:** Searches for `bidiagonal MRRR 2026 algorithm` found proposed methods but no unconditional theorem satisfying the stated bounds. **Formulation note:** the survey prints only one residual equation. Both are needed for the intended selected-SVD task; one-sided residuals alone do not define approximate singular triples.

**Admission obstacle:** An unrestricted constant depending on $u$ together with $nu\leq c$ bounds $n$ and permits even cubic work to be described as $O(nk)$. Uniform $O(nk)$ or an explicit $\operatorname{polylog}(1/u)$ allowance requires checking the source’s intended computational model. Until then, the original numerical challenge is preserved without claiming a precise admitted theorem target.

## Removed or withheld questions — not included in the count

- **Polynomial worst-case complete/rook pivoting growth:** excluded. Shah and Urschel, [*Entry growth in Gaussian elimination*](https://arxiv.org/abs/2608.19189), August 2026, Theorems 1.6–1.7, give quasipolynomial lower bounds. This is a recent preprint resolution claim, not an independently certified proof by this catalog.
- **Forsythe restart length two:** excluded because of the August 2026 Colbrook–Stepaniants–Townsend preprint cited in IE-01. The remaining general question is retained there.
- **Power-law-spectrum CG versus randomized coordinate descent, Simons Problem 2.4:** withheld following Chen et al., [*Iteris: Agentic Research Loops for Computational Mathematics*](https://arxiv.org/html/2606.02484v1#S4.SS2), June 2026, Theorem 1 and Appendix 6. It claims a fixed-parameter phase diagram; its rate bounds are expressly not sharp. Counting the original question without checking this claim would be misleading.
- **Higham's complex symmetric positive-definite growth bound:** excluded. Zhang, [*Sharp condition-number bounds for growth factors of Higham matrices in Gaussian elimination*](https://arxiv.org/abs/2604.23024), April 2026, identifies Drury's 2013 bound and develops a strict, quantitative refinement.
- **Broad GMRES convergence explanations, unspecified block-Lanczos rounding analyses, and unspecified MRRR input conditions:** retained only as source leads, not admitted as precise problems. The relevant source is [Amsel et al., §§2.5–2.6 and §3.4](https://arxiv.org/html/2602.05394v3). Additional work is needed to turn each into a quantifiable target without inventing a new problem or restating a known theorem.
