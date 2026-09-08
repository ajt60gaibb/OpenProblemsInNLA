# Positive matrix factorizations

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

- **Difficulty:** challenging
- **Importance:** interesting to specialist
- **Status:** open; checked 2026-09-08
- **Area:** structured positive semidefinite factorization

For each integer $n\ge5$, let $\mathcal I_n$ and $\mathcal J_n$ consist of the subsets of $\{1,\ldots,n\}$ of cardinalities $\lfloor n/2\rfloor$ and $\lceil n/2\rceil$, respectively. Define the nonnegative matrix

$$
M^{(n)}\in\mathbb R_+^{\mathcal I_n\times\mathcal J_n},
\qquad M^{(n)}_{I,J}=|I\cap J|.
$$

**Problem.** Determine $\operatorname{rank}_{\rm psd}(M^{(n)})$ exactly as a function of $n$, with real symmetric factors as defined above. The family is one problem; its individual orders are not separate catalog entries.

The source supplies the bounds

$$
\left\lceil\frac{\sqrt{1+8n}-1}{2}\right\rceil
\le \operatorname{rank}_{\rm psd}(M^{(n)})
\le 2\lceil\sqrt n\rceil.
$$

These matrices provide structured benchmarks for algorithms seeking small positive semidefinite factorizations.

**References.** Hamza Fawzi, João Gouveia, Pablo A. Parrilo, Richard Z. Robinson, and Rekha R. Thomas, [*Positive semidefinite rank*](https://arxiv.org/html/1407.4095), Mathematical Programming **153** (2015), 133–177, §9.1, Problem 9.2. Arnaud Vandaele, François Glineur, and Nicolas Gillis, [*Algorithms for Positive Semidefinite Factorization*](https://arxiv.org/pdf/1707.07953), Computational Optimization and Applications **71** (2018), 193–219, §4.2, preprint pp. 10–11.

**Status evidence.** The algorithm paper explicitly retains the unknown exact rank and uses known upper bounds in its experiments. Searches for “positive semidefinite rank Johnson scheme”, “positive semidefinite rank intersection matrix”, and “P5 psd rank” found no subsequent exact formula. The arXiv histories of both cited papers were checked; each lists only its original version. No newer explicit open-status confirmation was located.

<a id="pf-02"></a>

## PF-02 — Connectedness of minimal positive semidefinite factorization orbits

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; checked 2026-09-08
- **Area:** geometry of constrained matrix factorizations

Let $k\ge3$ and $p,q\ge1$ be integers. Suppose $M\in\mathbb R_+^{p\times q}$ satisfies

$$
\operatorname{rank}(M)=\frac{k(k+1)}2,
\qquad \operatorname{rank}_{\rm psd}(M)=k.
$$

Let $\mathcal F_k(M)$ be the set of all tuples $(A_1,\ldots,A_p,B_1,\ldots,B_q)$ in $(\mathbb S_+^k)^{p+q}$ satisfying $\operatorname{tr}(A_iB_j)=M_{ij}$ for every $i,j$. Give it the Euclidean subspace topology. Identify tuples under the changes of basis

$$
A_i\longmapsto S^\mathsf T A_iS,\qquad
B_j\longmapsto S^{-1}B_jS^{-\mathsf T},
\qquad S\in GL(k,\mathbb R).
$$

Give the resulting orbit space the quotient topology.

**Problem.** Is $\mathcal F_k(M)/GL(k,\mathbb R)$ connected for every $M$ satisfying these hypotheses?

The ordinary-rank hypothesis is part of the problem. The case $k=2$ is known to be connected. The question asks whether optimal factors can belong to separated families after changes of basis are identified.

**References.** Fawzi, Gouveia, Parrilo, Robinson, and Thomas, [*Positive semidefinite rank*](https://arxiv.org/html/1407.4095), §9.2, Problem 9.4. Richard Z. Robinson, [*The Positive Semidefinite Rank of Matrices and Polytopes*](https://digital.lib.washington.edu/server/api/core/bitstreams/4e9d6133-5d14-4071-9905-70bd7dfd530e/content), University of Washington dissertation (2015), Chapter 7, especially Proposition 7.0.8.

**Status evidence.** Searches for “psd factorizations connected”, “positive semidefinite factorization space connected”, and “psd factorization orbits connected 2026” found the original question and the known $k=2$ result, but no resolution under the displayed rank conditions. Universality or disconnectedness results for nonnegative vector factorizations do not by themselves answer this question. No recent explicit open-status confirmation was located.

<a id="pf-03"></a>

## PF-03 — Rational factors for rational completely positive boundary matrices

- **Difficulty:** extreme
- **Importance:** interesting to the community
- **Status:** open; checked 2026-09-08
- **Area:** exact certificates for nonnegative symmetric factorization

**Problem.** For every integer $n\ge5$ and every

$$
A\in\mathbb Q^{n\times n}\cap\partial\mathcal{CP}_n,
$$

does there exist a finite integer $m\ge1$ and a matrix $B\in\mathbb Q_{\ge0}^{n\times m}$ such that

$$
A=BB^\mathsf T?
$$

The width $m$ is unrestricted. In particular, it need not equal the real cp-rank or the order of $A$. This is an existence question for an exact rational certificate of complete positivity.

Rational matrices in the interior of $\mathcal{CP}_n$ have rational completely positive factors. Several boundary classes are also known, including matrices of rank at most two. The question concerns the remaining boundary matrices.

**References.** Abraham Berman and Naomi Shaked-Monderer, [*Completely Positive Matrices over Sets*](https://cot.mathres.org/issues/COT202523.pdf), Communications in Optimization Theory (2025), article 23, §2, Question 2.1 and the explicit boundary Open Problem, p. 2. Mathieu Dutour Sikirić, Achill Schürmann, and Frank Vallentin, [*Rational factorizations of completely positive matrices*](https://doi.org/10.1016/j.laa.2017.02.017), Linear Algebra and its Applications **523** (2017), 46–51, Theorem 1.1. Max Pfeffer and José Alejandro Samper, [*The Cone of $5\times5$ Completely Positive Matrices*](https://link.springer.com/article/10.1007/s00454-023-00620-y), Discrete & Computational Geometry **71** (2024), 442–466, §6, Problem 6.3, discusses the order-five boundary.

**Status evidence.** Searches for “rational completely positive 2026 boundary” and “completely positive rational 2025” located no general boundary resolution. Alexander Oertel and Achill Schürmann's [*Generalized Perfect Matrices*, latest arXiv v2](https://arxiv.org/html/2602.05841v2), submitted 2026-06-04, §6.1.1, still guarantees rational factors for interior matrices; its introduction describes the general rational-factorization algorithm conditionally on existence. Neither result resolves the displayed boundary question.

<a id="pf-04"></a>

## PF-04 — The maximum cp-rank in order six

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; checked 2026-09-08
- **Area:** size of nonnegative symmetric factorizations

**Problem.** Is every real completely positive matrix of order six a sum of at most nine nonnegative rank-one matrices? Equivalently, is

$$
\max_{A\in\mathcal{CP}_6}\operatorname{cpr}(A)=9,
$$

or, equivalently, does each $A\in\mathcal{CP}_6$ admit $A=BB^\mathsf T$ with $B\in\mathbb R_{\ge0}^{6\times9}$, allowing zero columns?

The lower bound nine is established. Order six is the unresolved case of the original Drew–Johnson–Loewy bound: order five satisfies it, whereas counterexamples exist in higher orders. It is included as the specific remaining case identified in the literature, rather than as one item in a dimension-by-dimension list.

A known reduction places a matrix attaining the order-six maximum on the boundary of $\mathcal{CP}_6$, with full ordinary rank and at least one zero entry. This reduction does not establish the nine-column bound.

**References.** Abraham Berman, Mirjam Dür, and Naomi Shaked-Monderer, [*Open problems in the theory of completely positive and copositive matrices*](https://journals.uwyo.edu/index.php/ela/article/download/1477/1477), Electronic Journal of Linear Algebra **29** (2015), 46–58, §4.2, p. 53. Naomi Shaked-Monderer, [*On the DJL conjecture for order 6*, corrected arXiv v3](https://arxiv.org/html/1501.02426v3), 2017-06-01; journal version in Operators and Matrices **11** (2017), 71–88, Theorem 1.1 and Corollary 3.2.

**Status evidence.** Searches for “DJL conjecture 2026”, “DJL conjecture 2025”, “cp-rank order 6 solved”, and “maximum cp-rank 6 2026” found no order-six proof or counterexample. The corrected v3 retains the question. Roger Behling, Douglas Gonçalves, Hugo Lara, and Harry Oviedo, [*A Projected Inexact Levenberg-Marquardt Method for the Completely Positive Matrix Factorization*](https://doi.org/10.1007/s10957-026-02950-2), Journal of Optimization Theory and Applications **209** (2026), article 9, §5.6, reproduces higher-order counterexamples to the general DJL conjecture, not an order-six resolution. The most recent explicit open statement verified for this exact case is the corrected 2017 source.

<a id="pf-05"></a>

## PF-05 — Infinitesimal rigidity detects unique size-two factors in the presence of zeros

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** explicitly conjectured in the August 2026 source; checked 2026-09-08.

Let $M\in\mathbb R_+^{p\times q}$ satisfy $\operatorname{rank}(M)=3$ and
$\operatorname{rank}_{\rm psd}(M)=2$, and fix any size-two factorization
$M_{ij}=\operatorname{tr}(A_iB_j)$. Zero entries of $M$ are allowed.

Call a collection of real symmetric matrices $(E_i,F_j)$ a feasible linear
direction if

$$
\operatorname{tr}(E_iB_j)+\operatorname{tr}(A_iF_j)=0\quad\text{for every }i,j
$$

and some $h>0$ satisfies $A_i+tE_i\succeq0$, $B_j+tF_j\succeq0$ for
all $i,j$ and $t\in[0,h)$. The trace constraint is imposed only to first
order; the perturbed factors need not represent $M$ at positive $t$.

**Problem.** Are the following conditions equivalent for every such factorization?

1. Every feasible linear direction has the form $E_i=dA_i$, $F_j=-dB_j$
   for one real scalar $d$ common to all factors.
2. Every other size-two factorization $(\widetilde A_i,\widetilde B_j)$ of
   $M$ satisfies $\widetilde A_i=S^\mathsf T A_iS$ and
   $\widetilde B_j=S^{-1}B_jS^{-\mathsf T}$ for one $S\in GL(2,\mathbb R)$.

This asks whether an infinitesimal test certifies uniqueness of the optimal
matrix factors up to changes of basis. Condition 1 is exactly the source's
2-infinitesimal rigidity: for size two, the relevant second-degree Taylor
polynomials are the complete principal minors, and Theorem 2.2 identifies the
trivial directions as the common scalings above.

**Reference and status.** K. Dawson, S. Hoşten, K. Kubjas, and L. Metsälampi,
[*Uniqueness of size-2 positive semidefinite matrix factorizations*, v2](https://arxiv.org/html/2410.18891v2),
31 August 2026, Definition 1, Remark 1, Theorem 2.2, and the conjecture immediately
after Theorem 5.2. Theorem 5.2 proves the assertion when every entry of $M$ is
strictly positive. Lemma 19 identifies local and global rigidity in the stated
rank class, so omitting the equivalent local condition does not weaken the
source's remaining conjecture. Searches for the title, PSD rigidity with zeros,
and later work found no resolution beyond this latest version.

## Exclusions and source leads — uncounted

- **Lorentz cones and the interior Ryshkov property:** Oertel and Schürmann's February 2026 v1 asks whether Lorentz cones have this property. Their [June 2026 v2, §7.3](https://arxiv.org/html/2602.05841v2) reports that the three-dimensional Lorentz cone does not. The old universal question is excluded. The broader geometric research direction remaining in v2 has not been converted into additional entries.
- **Hadamard powers preserving factor width, and equality of real/complex factor-width rank:** Question 1 and Conjecture 1 of Nathaniel Johnston, Shirin Moein, and Sarah Plosker, [*The factor width rank of a matrix*](https://arxiv.org/html/2405.11556v2), Linear Algebra and its Applications **716** (2025), 32–59, have claimed resolutions in Yaroslav Shitov, [*Using the FitzGerald–Horn theorem with GPT-5.5*](https://www.researchgate.net/publication/408732286_Using_the_FitzGerald--Horn_theorem_with_GPT-55), author-posted preprint, 2026-07-10, DOI 10.13140/RG.2.2.24873.15204. Its abstract asserts the power theorem and a counterexample to real/complex equality. Excluded pending assessment of those proofs.
- **Maximum integer cp-rank in order two:** The 2025 *Completely Positive Matrices over Sets* question is superseded by the 2025 paper [*11 can be reduced to 10*](https://journals.uwyo.edu/index.php/ela/article/download/9681/7201/26763) and the claimed sharp bound nine in Shitov's [*Largest CP-ranks of $2\times2$ matrices over $\mathbb Z$, via GPT*](https://www.researchgate.net/publication/407030413_Largest_CP-ranks_of_2_x_2_matrices_over_Z_via_GPT), 2026-06-13, DOI 10.13140/RG.2.2.23558.33601. Excluded; this concerns integer factors and is distinct from PF-03.
- **The unrestricted DJL formula:** The proposed equality $\max_{A\in\mathcal{CP}_n}\operatorname{cpr}(A)=\lfloor n^2/4\rfloor$ for all $n\ge4$ is false. See Immanuel M. Bomze, Werner Schachinger, and Reinhard Ullrich, [*From seven to eleven: completely positive matrices with high cp-rank*](https://optimization-online.org/wp-content/uploads/2014/01/4206.pdf), Linear Algebra and its Applications **459** (2014), 208–221. PF-04 retains only the explicitly unresolved order six.
- **A printed perturbation question with inconsistent distances:** Pfeffer and Samper [§6, Problem 6.2](https://link.springer.com/article/10.1007/s00454-023-00620-y) compares the distances of $A,\widetilde A$ and $BB^\mathsf T,\widetilde B\widetilde B^\mathsf T$ while calling $B,\widetilde B$ their factor matrices. These are the same pairs of matrices. The displayed conditions conflict for sufficiently small requested perturbations. An intended question about distances between factors or factor orbits needs clarification; none is silently substituted.
- **An explicit description of the cp-rank-five boundary inside $\mathcal{CP}_5$:** Pfeffer and Samper §6, Problem 6.1 is a useful source lead. A precise nontrivial deliverable beyond general semialgebraic quantifier elimination, faithful to the proposed factor zero-pattern description in §5.5, has not yet been fixed. It is uncounted.
- **General hardness of computing positive semidefinite rank:** The generic hardness request in the 2015 PSD-rank survey is superseded by Yaroslav Shitov, [*The Complexity of Positive Semidefinite Matrix Factorization*](https://arxiv.org/abs/1606.09065), SIAM Journal on Optimization **27** (2017), 1898–1909. Its existential-theory-of-the-reals completeness result is not an open problem. This exclusion does not claim to settle every special tightness test mentioned alongside the old question.
