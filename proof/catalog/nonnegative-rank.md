# Exact nonnegative ranks

This chapter contains **4 admitted problems**. Ratings are editorial. Status
searches were checked on **2026-09-08** and have the limits described in each
entry. All factorizations are over the real numbers. For
$X\in\mathbb R_{\ge0}^{m\times n}$, define

$$
\operatorname{rank}_+(X)=\min\{r\ge0:X=WH,\quad
W\in\mathbb R_{\ge0}^{m\times r},\ H\in\mathbb R_{\ge0}^{r\times n}\}.
$$

These questions concern the exact rank required by a constrained low-rank
factorization, including structured benchmarks used by numerical NMF methods.

<a id="nr-01"></a>

## NR-01 — Exact nonnegative rank of regular polygon slack matrices

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; checked 2026-09-08
- **Area:** structured nonnegative matrix factorization

For each integer $n\ge3$, define the $n\times n$ nonnegative matrix

$$
S_n(i,j)=\cos(\pi/n)-\cos\bigl((2i+1-2j)\pi/n\bigr),
\qquad 0\le i,j<n.
$$

It is the slack matrix obtained from the vertices of the regular $n$-gon on
the unit circle and its supporting facet inequalities.

**Problem.** With $k=\lceil\log_2 n\rceil$, is it true for every $n\ge3$ that

$$
\operatorname{rank}_+(S_n)=
\begin{cases}
2k-1,&2^{k-1}<n\le 2^{k-1}+2^{k-2},\\
2k,&2^{k-1}+2^{k-2}<n\le2^k?
\end{cases}
$$

**References.** Arnaud Vandaele, Nicolas Gillis, François Glineur, and Daniel
Tuyttens, [*Heuristics for Exact Nonnegative Matrix Factorization*](https://arxiv.org/html/1411.7245),
Journal of Global Optimization **65** (2016), 369–400, §6.2, Conjecture 2.
Vandaele, Gillis, and Glineur,
[*On the Linear Extension Complexity of Regular n-gons*](https://arxiv.org/abs/1505.08031),
Linear Algebra and its Applications **521** (2017), 217–239, proves the
corresponding upper bound. Nicolas Gillis,
[*Nonnegative Matrix Factorization*](https://orbi.umons.ac.be/bitstream/20.500.12907/42337/1/NMFbook_SIAM_reprint.pdf),
SIAM, 2020, §3.6.3.4, p. 90.

**Status evidence.** Baeckelant, Vandaele, and Gillis,
[*Computing Lower Bounds on the Nonnegative Rank via Non-Convex Optimization Solvers*](https://arxiv.org/html/2605.14058v2),
revised July 6, 2026, Appendix A.2, still identifies sharpness as conjectural.
Searches for the conjecture and regular-polygon nonnegative ranks in 2025–2026
found no subsequent resolution. The family is counted once.

<a id="nr-02"></a>

## NR-02 — Additivity for Cartesian-product slack matrices

- **Difficulty:** extreme
- **Importance:** interesting to the community
- **Status:** open; checked 2026-09-08
- **Area:** nonnegative rank and polyhedral optimization

Let $P\subset\mathbb R^d$ and $Q\subset\mathbb R^e$ be full-dimensional
polytopes with $d,e\ge1$. Let $S\in\mathbb R_{\ge0}^{m\times n}$ and
$T\in\mathbb R_{\ge0}^{p\times q}$ be their slack matrices: rows correspond
to all facets in irredundant inequality descriptions, columns to all vertices,
and each entry is the right-hand side minus the left-hand side of that facet
inequality at that vertex. Construct $C\in\mathbb R_{\ge0}^{(m+p)\times nq}$
by giving it one column for each pair $(i,j)$ of vertices:

$$
C[:,(i,j)]=\begin{pmatrix}S[:,i]\\T[:,j]\end{pmatrix}.
$$

**Problem.** Is

$$
\operatorname{rank}_+(C)=\operatorname{rank}_+(S)+\operatorname{rank}_+(T)
$$

always true? The hypotheses that $S,T$ are polytope slack matrices are part of
the question. Through the slack-factorization theorem, this also asks whether
the minimum number of inequalities in an extended formulation is additive
under Cartesian products.

**References.** Gillis, [*Nonnegative Matrix Factorization*](https://orbi.umons.ac.be/bitstream/20.500.12907/42337/1/NMFbook_SIAM_reprint.pdf),
§3.6.5, pp. 93–94. Hans Raj Tiwary, Stefan Weltge, and Rico Zenklusen,
[*Extension complexities of Cartesian products involving a pyramid*](https://arxiv.org/abs/1702.01959),
Information Processing Letters **128** (2017), 11–13, introduction and main
theorem.

**Status evidence.** The equality is proved when at least one factor is a
pyramid. Searches for Cartesian-product extension-complexity additivity,
counterexamples, and 2025–2026 developments found no general resolution.
Stefan Weltge poses the general equality again in the
[Cargèse workshop open problems](https://www.cargese.org/2022/open-problems.pdf),
September 20, 2022, p. 1. This is the latest explicit general open-status
confirmation located; its age is a limitation of this entry.

<a id="nr-03"></a>

## NR-03 — Full nonnegative rank of the quadratic correlation matrix

- **Difficulty:** extreme
- **Importance:** broadly interesting
- **Status:** open; checked 2026-09-08
- **Area:** exact NMF and lower bounds for optimization formulations

For each integer $n\ge3$, let $C_n$ be the $2^n\times2^n$ matrix indexed by
$a,b\in\{0,1\}^n$ and defined by

$$
C_n(a,b)=(1-a^{\mathsf T}b)^2.
$$

**Problem.** Is $\operatorname{rank}_+(C_n)=2^n$ for every $n\ge3$?
All entries, including those for $a^{\mathsf T}b>1$, are fixed by this formula.

The matrix has ordinary rank $1+n(n+1)/2$ and is a submatrix of a slack matrix
of the correlation polytope formed from valid, possibly redundant inequalities.
The conjecture therefore asks for a large
separation between ordinary and nonnegative matrix rank with consequences for
linear programming representations.

**References.** Vandaele, Gillis, Glineur, and Tuyttens,
[*Heuristics for Exact Nonnegative Matrix Factorization*](https://arxiv.org/html/1411.7245),
§6.4, Conjecture 4. Gillis,
[*Nonnegative Matrix Factorization*](https://orbi.umons.ac.be/bitstream/20.500.12907/42337/1/NMFbook_SIAM_reprint.pdf),
§3.7, p. 96, using the name $U_n$ for this fixed matrix.

**Status evidence.** Baeckelant et al.,
[*Computing Lower Bounds on the Nonnegative Rank via Non-Convex Optimization Solvers*](https://arxiv.org/html/2605.14058v2),
§6.7 and Appendix A.4, still states the full-rank conjecture. Searches for its
resolution found none. Sergeev's July 2026
[*Upper bounds for the monotone rank of the unique disjointness matrix*](https://arxiv.org/abs/2607.27014)
concerns ranks of a **partial** unique-disjointness matrix with unspecified
entries when $a^{\mathsf T}b>1$; those bounds do not determine the rank of this
prescribed completion. The open $n=3$ instance is not counted separately.

<a id="nr-04"></a>

## NR-04 — The nonnegative rank of the nine-point distance matrix

- **Difficulty:** hard
- **Importance:** interesting to specialist
- **Status:** open; checked 2026-09-08
- **Area:** exact factorization of Euclidean distance matrices

Let $D\in\mathbb R_{\ge0}^{9\times9}$ have entries
$D_{ij}=(i-j)^2$ for $1\le i,j\le9$.

**Problem.** Does there exist an exact factorization
$D=WH$ with $W\in\mathbb R_{\ge0}^{9\times6}$ and
$H\in\mathbb R_{\ge0}^{6\times9}$? Equivalently, is
$\operatorname{rank}_+(D)=6$ or $7$?

**References.** Baeckelant, Vandaele, and Gillis,
[*Computing Lower Bounds on the Nonnegative Rank via Non-Convex Optimization Solvers*](https://arxiv.org/html/2605.14058v2),
Appendix A.1, Table 6 and its final paragraph, expressly isolates this case.
Pavel Hrubeš, *On the nonnegative rank of distance matrices*, Information
Processing Letters **112** (2012), 457–461, supplies the upper-bound construction
cited there.

**Status evidence.** The July 2026 revision records bounds $6\le
\operatorname{rank}_+(D)\le7$ and explicitly calls the exact value open.
Targeted searches for the nine-point linear Euclidean distance matrix and
subsequent nonnegative-rank results found no resolution. This is a named
unresolved benchmark in the source, rather than an arbitrary specialization
of a separately counted general problem.
