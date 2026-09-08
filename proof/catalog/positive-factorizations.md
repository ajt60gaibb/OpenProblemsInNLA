# Positive matrix factorizations

> Legacy source map and screening notes. Admitted statements have moved to category/problem folders. Follow the links below or [browse the new index](../../CATALOG.md). Shared notation and uncounted material are retained here as the historical source record.

This chapter contains **5 admitted problems**. The labels are editorial assessments, not quotations from the sources. “Open” means that an explicit source question was identified and the documented literature search found no resolution through **2026-09-08**; this is not a proof that none exists. The exclusions below are uncounted.

Write $\mathbb S_+^k$ for the cone of real symmetric positive semidefinite $k\times k$ matrices. For an entrywise nonnegative matrix $M\in\mathbb R_+^{p\times q}$, its **real positive semidefinite rank** is

$$
\operatorname{rank}_{\rm psd}(M)
=\min\{k\ge1:\ \exists A_1,\ldots,A_p,B_1,\ldots,B_q\in\mathbb S_+^k,\quad
M_{ij}=\operatorname{tr}(A_iB_j)\ \text{for all }i,j\}.
$$

This definition concerns a family of matrix factors indexed by the rows and columns of $M$.

A symmetric matrix $A$ is **completely positive** if $A=BB^\mathsf T$ for an entrywise nonnegative real matrix $B$ with finitely many columns. Let $\mathcal{CP}_n$ be the cone of these matrices of order $n$. Its **cp-rank**, $\operatorname{cpr}(A)$, is the minimum number of columns in such a factor, with $\operatorname{cpr}(0)=0$. Boundaries and interiors below use the usual Euclidean topology on the vector space of real symmetric matrices.

<a id="pf-01"></a>

## PF-01 — Exact positive semidefinite rank of subset-intersection matrices

[Open the problem folder](../../nonnegative-and-positive-factorizations/PF-01/README.md) · [PDF](../../nonnegative-and-positive-factorizations/PF-01/problem.pdf) · [LaTeX](../../nonnegative-and-positive-factorizations/PF-01/problem.tex)


<a id="pf-02"></a>

## PF-02 — Connectedness of minimal positive semidefinite factorization orbits

[Open the problem folder](../../nonnegative-and-positive-factorizations/PF-02/README.md) · [PDF](../../nonnegative-and-positive-factorizations/PF-02/problem.pdf) · [LaTeX](../../nonnegative-and-positive-factorizations/PF-02/problem.tex)


<a id="pf-03"></a>

## PF-03 — Rational factors for rational completely positive boundary matrices

[Open the problem folder](../../nonnegative-and-positive-factorizations/PF-03/README.md) · [PDF](../../nonnegative-and-positive-factorizations/PF-03/problem.pdf) · [LaTeX](../../nonnegative-and-positive-factorizations/PF-03/problem.tex)


<a id="pf-04"></a>

## PF-04 — The maximum cp-rank in order six

[Open the problem folder](../../nonnegative-and-positive-factorizations/PF-04/README.md) · [PDF](../../nonnegative-and-positive-factorizations/PF-04/problem.pdf) · [LaTeX](../../nonnegative-and-positive-factorizations/PF-04/problem.tex)


<a id="pf-05"></a>

## PF-05 — Infinitesimal rigidity detects unique size-two factors in the presence of zeros

[Open the problem folder](../../nonnegative-and-positive-factorizations/PF-05/README.md) · [PDF](../../nonnegative-and-positive-factorizations/PF-05/problem.pdf) · [LaTeX](../../nonnegative-and-positive-factorizations/PF-05/problem.tex)


## Exclusions and source leads — uncounted

- **Lorentz cones and the interior Ryshkov property:** Oertel and Schürmann's February 2026 v1 asks whether Lorentz cones have this property. Their [June 2026 v2, §7.3](https://arxiv.org/html/2602.05841v2) reports that the three-dimensional Lorentz cone does not. The old universal question is excluded. The broader geometric research direction remaining in v2 has not been converted into additional entries.
- **Hadamard powers preserving factor width, and equality of real/complex factor-width rank:** Question 1 and Conjecture 1 of Nathaniel Johnston, Shirin Moein, and Sarah Plosker, [*The factor width rank of a matrix*](https://arxiv.org/html/2405.11556v2), Linear Algebra and its Applications **716** (2025), 32–59, have claimed resolutions in Yaroslav Shitov, [*Using the FitzGerald–Horn theorem with GPT-5.5*](https://www.researchgate.net/publication/408732286_Using_the_FitzGerald--Horn_theorem_with_GPT-55), author-posted preprint, 2026-07-10, DOI 10.13140/RG.2.2.24873.15204. Its abstract asserts the power theorem and a counterexample to real/complex equality. Excluded pending assessment of those proofs.
- **Maximum integer cp-rank in order two:** The 2025 *Completely Positive Matrices over Sets* question is superseded by the 2025 paper [*11 can be reduced to 10*](https://journals.uwyo.edu/index.php/ela/article/download/9681/7201/26763) and the claimed sharp bound nine in Shitov's [*Largest CP-ranks of $2\times2$ matrices over $\mathbb Z$, via GPT*](https://www.researchgate.net/publication/407030413_Largest_CP-ranks_of_2_x_2_matrices_over_Z_via_GPT), 2026-06-13, DOI 10.13140/RG.2.2.23558.33601. Excluded; this concerns integer factors and is distinct from PF-03.
- **The unrestricted DJL formula:** The proposed equality $\max_{A\in\mathcal{CP}_n}\operatorname{cpr}(A)=\lfloor n^2/4\rfloor$ for all $n\ge4$ is false. See Immanuel M. Bomze, Werner Schachinger, and Reinhard Ullrich, [*From seven to eleven: completely positive matrices with high cp-rank*](https://optimization-online.org/wp-content/uploads/2014/01/4206.pdf), Linear Algebra and its Applications **459** (2014), 208–221. PF-04 retains only the explicitly unresolved order six.
- **A printed perturbation question with inconsistent distances:** Pfeffer and Samper [§6, Problem 6.2](https://link.springer.com/article/10.1007/s00454-023-00620-y) compares the distances of $A,\widetilde A$ and $BB^\mathsf T,\widetilde B\widetilde B^\mathsf T$ while calling $B,\widetilde B$ their factor matrices. These are the same pairs of matrices. The displayed conditions conflict for sufficiently small requested perturbations. An intended question about distances between factors or factor orbits needs clarification; none is silently substituted.
- **An explicit description of the cp-rank-five boundary inside $\mathcal{CP}_5$:** Pfeffer and Samper §6, Problem 6.1 is a useful source lead. A precise nontrivial deliverable beyond general semialgebraic quantifier elimination, faithful to the proposed factor zero-pattern description in §5.5, has not yet been fixed. It is uncounted.
- **General hardness of computing positive semidefinite rank:** The generic hardness request in the 2015 PSD-rank survey is superseded by Yaroslav Shitov, [*The Complexity of Positive Semidefinite Matrix Factorization*](https://arxiv.org/abs/1606.09065), SIAM Journal on Optimization **27** (2017), 1898–1909. Its existential-theory-of-the-reals completeness result is not an open problem. This exclusion does not claim to settle every special tightness test mentioned alongside the old question.
