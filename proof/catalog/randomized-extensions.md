# Hierarchical and general structured matrix approximation

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

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; checked 2026-09-08
- **Area:** structured low-rank matrix approximation

**Problem.** Do absolute constants $C,c>0$ and a uniform randomized algorithm exist that, given the entries of any $A\in\mathbb R^{N\times N}$ and integers $k,L\ge1$ with $N=2^{L+1}k$, returns $B\in\mathcal S_{L,k}$ using $O(N^c)$ arithmetic operations and satisfies

$$
\mathbb E\|A-B\|_F^2\le C\,E_{L,k}(A)?
$$

The exponent and approximation constant must be independent of $k,L,A$. A deterministic algorithm is allowed. The output must retain rank at most $k$.

**Reference.** Noah Amsel, Tyler Chen, Feyza Duman Keles, Diana Halikias, Cameron Musco, Christopher Musco, and David Persson, [*Quasi-optimal Hierarchically Semi-separable Matrix Approximation*](https://arxiv.org/html/2505.16937v2), SIAM Journal on Matrix Analysis and Applications **47** (2026), 586–621, §3.4; Theorems 6 and 12. That section expressly asks for a polynomial-time constant-factor approximation.

**Status evidence.** The known squared-error factor is $O(L)$. The lower bound near $2$ concerns the analyzed greedy algorithm, not all algorithms. Searches for “HSS constant-factor approximation 2026” and “hierarchically semiseparable approximation constant 2026” found no resolution. The latest arXiv version is v2, September 6, 2025; the [journal version](https://doi.org/10.1137/25M176622X) appeared online May 8, 2026.

<a id="re-02"></a>

## RE-02 — HSS approximation from a number of matvecs independent of depth

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; checked 2026-09-08
- **Area:** randomized matrix compression

**Problem.** Do absolute constants $C_q,C_e,c>0$ and a uniform randomized algorithm exist that, for every $k,L\ge1$ and every $A\in\mathbb R^{N\times N}$, $N=2^{L+1}k$, accesses $A$ solely through at most $C_qk$ matrix–vector queries and returns $B\in\mathcal S_{L,k}$ satisfying

$$
\mathbb E\|A-B\|_F^2\le C_e L\,E_{L,k}(A),
$$

with at most $O(N^c)$ additional arithmetic operations? Queries may be adaptive. The budget counts both transpose and forward products and is a bound on every execution.

**References.** Amsel et al., [*Quasi-optimal Hierarchically Semi-separable Matrix Approximation*](https://arxiv.org/html/2505.16937v2), §1.2, Theorem 13, §§4.4–5. James Levitt and Per-Gunnar Martinsson, [*Linear-Complexity Black-Box Randomized Compression of Rank-Structured Matrices*](https://arxiv.org/pdf/2205.02990v3), SIAM Journal on Scientific Computing **46** (2024), A1747–A1763, Algorithm 4.1 and Remark 4.3.

**Status evidence.** The proved guarantee uses $O(kL)$ queries. Reusing sketches reduces the query count, but its approximation guarantee remains unproved. Searches for “HSS O(k) approximation 2026 matvec” and “HSS approximation logarithmic 2026” found no resolution. Levitt–Martinsson's latest arXiv version is v3, submitted June 21, 2024. Christopher Musco's [February 2026 ICERM slides](https://app.icerm.brown.edu/assets/568/10574/10574_5858_Musco_020420261630_Slides.pdf), numbered slide 14, still list $O(k\log N)$ queries for HSS approximation.

RE-01 permits full access and asks for a constant error factor. RE-02 retains the known dependence of the error factor on depth and asks for fewer queries. Neither target directly implies the other.

<a id="re-03"></a>

## RE-03 — Optimal matvec query complexity of HODLR approximation

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; checked 2026-09-08
- **Area:** information complexity of hierarchical matrix approximation

Let $n=2^Lk$ with integers $k\ge1,L\ge2$, and $0<\varepsilon<1/2$. Define $\mathcal H_{n,k}$ recursively: a matrix of order at most $k$ is unrestricted; at a larger node, the two equally sized diagonal blocks must satisfy the same definition, and each off-diagonal block must have rank at most $k$.

Let $q_*(n,k,\varepsilon)$ be the smallest worst-case number of queries with which a randomized adaptive algorithm, given only oracle access to an arbitrary $A\in\mathbb R^{n\times n}$, returns $B\in\mathcal H_{n,k}$ such that

$$
\Pr\!\left[
\|A-B\|_F\le(1+\varepsilon)
\min_{H\in\mathcal H_{n,k}}\|A-H\|_F
\right]\ge0.99
$$

for every $A$. Here only oracle calls are charged: arbitrary measurable computations between queries are allowed. This is an information complexity question.

**Problem.** Determine $q_*(n,k,\varepsilon)$ up to universal multiplicative constants, including its joint dependence on $k,L,\varepsilon$.

**Reference.** Tyler Chen, Feyza Duman Keles, Diana Halikias, Cameron Musco, Christopher Musco, and David Persson, [*Near-optimal hierarchical matrix approximation from matrix-vector products*](https://arxiv.org/pdf/2407.04686v2), SODA 2025, 2656–2692, Definition 1.1, Problem 1.1, Theorems 1.1–1.2, end of §6, and §8.

The known upper bound is $O(\min\{n,kL^4/\varepsilon^3\})$. The source proves $\Omega(kL+k/\varepsilon)$ in its regime $n\ge c_0k/\varepsilon$ for a sufficiently large absolute $c_0$; this restriction matters near the full-recovery threshold.

**Status evidence.** The latest arXiv version is v2, October 24, 2024. Searches for “HODLR query complexity 2026” and “HODLR approximation 2026 lower bound” found no matching improvement. Musco's [February 2026 ICERM slides](https://app.icerm.brown.edu/assets/568/10574/10574_5858_Musco_020420261630_Slides.pdf), numbered slide 14, retain the stated upper bound. No later explicit open-status confirmation was located.

<a id="re-05"></a>

## RE-05 — Pure relative error for approximation by a linear matrix family

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; checked 2026-09-08
- **Area:** matrix sketching and structured least squares

Let $1\le q\le n^2$ and suppose linearly independent matrices $P_1,\ldots,P_q\in\mathbb R^{n\times n}$ are given explicitly. Write

$$
\mathcal L=\operatorname{span}_{\mathbb R}\{P_1,\ldots,P_q\}.
$$

An arbitrary $A\in\mathbb R^{n\times n}$ is accessible only through matrix–vector queries.

**Problem.** Do absolute constants $C>0$, integers $a,b\ge0$, and a uniform randomized algorithm exist that, for every $0<\varepsilon<1/2$, use at most

$$
C\sqrt q\,\varepsilon^{-a}
\bigl[1+\log(2+q)+\log(1/\varepsilon)\bigr]^b
$$

queries and return coefficients $c_1,\ldots,c_q\in\mathbb R$ such that, with probability at least $0.99$,

$$
\left\|A-\sum_{j=1}^q c_jP_j\right\|_F
\le(1+\varepsilon)\min_{D\in\mathcal L}\|A-D\|_F?
$$

Adaptive queries and unrestricted computation between queries are permitted. The displayed bound must hold uniformly over the basis and the target.

**Reference.** Noah Amsel, Pratyush Avi, Tyler Chen, Feyza Duman Keles, Chinmay Hegde, Christopher Musco, Cameron Musco, and David Persson, [*Query Efficient Structured Matrix Learning*](https://arxiv.org/html/2507.19290v2), COLT 2026, PMLR **336**, 158–194, §5, linear-family conjecture; Corollary 1 has an additional term $\alpha\|A\|_F$ and query dependence on $\alpha$.

**Status evidence.** The August 21, 2026 revision explicitly retains this question. Searches for “linear matrix families pure relative error” and “linearly parameterized matrix relative error 2026” found no resolution. Its abstract update resolves a related finite-family problem; finite-family discretization still produces additive error and does not automatically supply the displayed guarantee. See the exclusion below.

<a id="re-06"></a>

## RE-06 — Nonadaptive queries for finite-family matrix approximation

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; checked 2026-09-08
- **Area:** nonadaptive matrix sketching

Let $n\ge1$, let $\mathcal F\subset\mathbb R^{n\times n}$ be explicitly given with $M=|\mathcal F|\ge2$, and let $A\in\mathbb R^{n\times n}$ be accessible only through matrix–vector queries. Set $t=\log(2M)$.

**Problem.** Do absolute constants $C>0$, integer $b\ge0$, and a uniform randomized algorithm exist that, for every $0<\varepsilon<1/2$, choose all query vectors and all choices between $A$ and $A^\mathsf T$ before receiving any oracle answers, make at most

$$
C\sqrt t\,\varepsilon^{-2}
\bigl[1+\log(2+t)+\log(1/\varepsilon)\bigr]^b
$$

queries, and return $B\in\mathcal F$ such that

$$
\Pr\!\left[\|A-B\|_F\le(3+\varepsilon)
\min_{D\in\mathcal F}\|A-D\|_F\right]\ge0.99?
$$

Query choices may depend on $\mathcal F,\varepsilon$ and randomness. Only oracle calls are charged; candidate processing and processing of the answers are unrestricted.

**References.** Amsel et al., [*Query Efficient Structured Matrix Learning*](https://arxiv.org/html/2507.19290v2), §5, adaptivity question. Christopher Musco, [*Structured Matrix Learning from Matrix-Vector Products*](https://app.icerm.brown.edu/assets/568/10574/10574_5858_Musco_020420261630_Slides.pdf), ICERM, February 4, 2026, numbered slide 23.

**Status evidence.** Both sources explicitly ask whether adaptivity is necessary; the paper's August 21, 2026 revision retains the question. Searches for “finite matrix approximation adaptivity 2026” and the paper identifier with “non-adaptive” found no resolution. The abstract's linked finite-family improvement, Theorem 1.2, uses two rounds after receiving a constant-factor warm start: its left query vectors depend on the first round's answers. It does not supply the required nonadaptive algorithm.

## Excluded and uncounted leads

**Finite-family relative error (former RE-04): excluded.** The August 21, 2026 version of [*Query Efficient Structured Matrix Learning*](https://arxiv.org/html/2507.19290v2) still lists the finite-family $(1+\varepsilon)$ conjecture in §5, but an update immediately after the abstract states that it has been resolved. The authors link a [proof of the improved approximation factor](https://github.com/PratyushAvi/Structured-Matrix-Learning/blob/main/1%2Beps-finite-family-approximation.pdf), which they report human-verified as of August 2026. The stale §5 question is therefore not admitted. This update is absent from the standalone arXiv abstract page.

The [Simons workshop collection, v3](https://arxiv.org/html/2602.05394v3), was revised August 21, 2026 and incorporates status updates through August 20. Its Problem 4.5 motivates the hierarchical approximation references above. Its Problem 4.4 on kernel selection and Problem 4.5 on adaptive partitions were not added separately: the former requests suitable hypotheses, and the latter leaves the admissible partitions and algorithmic target unspecified. Choosing these would create new conjectures rather than extract precise source statements.

The displayed nonlinear eigenvector-dependent problem in §6.2 is also uncounted. The terms with equal indices can multiply two Hermitian factors acting on the same component without ensuring a Hermitian product, and the requested linear dependence on the number of components needs an input/preprocessing model for densely specified pair interactions. A faithful precise entry requires clarification of these source-level issues.

The remaining precise questions in chapters 4–6 were compared with the existing catalog and the v3 resolution notes. No additional dimension-specialized or renamed versions were counted.
