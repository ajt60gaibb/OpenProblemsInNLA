# Hierarchical and general structured matrix approximation

> Legacy source map and screening notes. Admitted statements have moved to category/problem folders. Follow the links below or [browse the new index](../../CATALOG.md). Shared notation and uncounted material are retained here as the historical source record.

This chapter contains **5 admitted problems**. Ratings are editorial. “Open” records the source question and the literature search through **2026-09-08**, not a proof that no resolution exists. These problems concern approximation of arbitrary input matrices; exact recovery of a matrix already possessing the requested structure is a different, easier task.

Use exact real arithmetic, with comparisons, standard Gaussian sampling, and exact SVDs available as primitives; charge an SVD of an $a\times b$ matrix $O(ab\min(a,b))$ operations. This states the idealized arithmetic model used here, rather than a finite precision or bit complexity claim. A matrix–vector query returns either $Av$ or $A^\mathsf Tv$ for one chosen real vector $v$; both types count toward the total. Randomized guarantees are for every fixed input, with probability or expectation over the algorithm's randomness.

For $N=2^{L+1}k$, $k,L\ge1$, form the perfect binary tree that successively halves the ordered index set $[N]=\{1,\ldots,N\}$ until every leaf contains $2k$ indices. Define $\mathcal S_{L,k}$ to contain precisely the real $N\times N$ matrices $B$ such that, for every nonroot node $I$ of this tree,

$$
\operatorname{rank}B[I,[N]\setminus I]\le k,
\qquad
\operatorname{rank}B[[N]\setminus I,I]\le k.
$$

This is the HSS class with rank at most $k$, including its constraints across levels. There is no restriction inside a leaf diagonal block. Set

$$
E_{L,k}(A)=\min_{B\in\mathcal S_{L,k}}\|A-B\|_F^2.
$$

The minimum exists. The rank definition follows Stefano Massei, Leonardo Robol, and Daniel Kressner, [*hm-toolbox: MATLAB Software for HODLR and HSS Matrices*](https://arxiv.org/pdf/1909.07909v3), SIAM Journal on Scientific Computing **42** (2020), C43–C68, §2.2, Definition 3. Equivalence with the telescoping representation and existence of a minimizer are recorded in Amsel et al., cited below, Definition 3 and Appendix D.

<a id="re-01"></a>

## RE-01 — Constant-factor HSS approximation in polynomial time

[Open the problem folder](../../randomized-and-low-rank-approximation/RE-01/README.md) · [PDF](../../randomized-and-low-rank-approximation/RE-01/problem.pdf) · [LaTeX](../../randomized-and-low-rank-approximation/RE-01/problem.tex)


<a id="re-02"></a>

## RE-02 — HSS approximation from a number of matvecs independent of depth

[Open the problem folder](../../randomized-and-low-rank-approximation/RE-02/README.md) · [PDF](../../randomized-and-low-rank-approximation/RE-02/problem.pdf) · [LaTeX](../../randomized-and-low-rank-approximation/RE-02/problem.tex)


<a id="re-03"></a>

## RE-03 — Optimal matvec query complexity of HODLR approximation

[Open the problem folder](../../randomized-and-low-rank-approximation/RE-03/README.md) · [PDF](../../randomized-and-low-rank-approximation/RE-03/problem.pdf) · [LaTeX](../../randomized-and-low-rank-approximation/RE-03/problem.tex)


<a id="re-05"></a>

## RE-05 — Pure relative error for approximation by a linear matrix family

[Open the problem folder](../../randomized-and-low-rank-approximation/RE-05/README.md) · [PDF](../../randomized-and-low-rank-approximation/RE-05/problem.pdf) · [LaTeX](../../randomized-and-low-rank-approximation/RE-05/problem.tex)


<a id="re-06"></a>

## RE-06 — Nonadaptive queries for finite-family matrix approximation

[Open the problem folder](../../randomized-and-low-rank-approximation/RE-06/README.md) · [PDF](../../randomized-and-low-rank-approximation/RE-06/problem.pdf) · [LaTeX](../../randomized-and-low-rank-approximation/RE-06/problem.tex)


## Excluded and uncounted leads

**Finite-family relative error (former RE-04): excluded.** The August 21, 2026 version of [*Query Efficient Structured Matrix Learning*](https://arxiv.org/html/2507.19290v2) still lists the finite-family $(1+\varepsilon)$ conjecture in §5, but an update immediately after the abstract states that it has been resolved. The authors link a [proof of the improved approximation factor](https://github.com/PratyushAvi/Structured-Matrix-Learning/blob/main/1%2Beps-finite-family-approximation.pdf), which they report human-verified as of August 2026. The stale §5 question is therefore not admitted. This update is absent from the standalone arXiv abstract page.

The [Simons workshop collection, v3](https://arxiv.org/html/2602.05394v3), was revised August 21, 2026 and incorporates status updates through August 20. Its Problem 4.5 motivates the hierarchical approximation references above. Its Problem 4.4 on kernel selection and Problem 4.5 on adaptive partitions were not added separately: the former requests suitable hypotheses, and the latter leaves the admissible partitions and algorithmic target unspecified. Choosing these would create new conjectures rather than extract precise source statements.

The displayed nonlinear eigenvector-dependent problem in §6.2 is also uncounted. The terms with equal indices can multiply two Hermitian factors acting on the same component without ensuring a Hermitian product, and the requested linear dependence on the number of components needs an input/preprocessing model for densely specified pair interactions. A faithful precise entry requires clarification of these source-level issues.

The remaining precise questions in chapters 4–6 were compared with the existing catalog and the v3 resolution notes. No additional dimension-specialized or renamed versions were counted.
