# MI-32 — Spectral norms of independent entries with regular moment growth

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Expected spectral norms of inhomogeneous random matrices  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** The missing upper estimate must account for localized random fluctuations across all variance profiles. Even weighted random signs retain an iterated-logarithm gap. A sharp estimate would improve quantitative understanding of the largest singular value in random matrix models.

## Statement

For a real random variable $Z$ and $r>0$, write
$\|Z\|_{L_r}=(\mathbb E|Z|^r)^{1/r}$. Fix $\alpha\ge1$. Let
$X=(X_{ij})\in\mathbb R^{n\times n}$ have independent mean-zero entries
with finite absolute moments of every order, satisfying

$$\|X_{ij}\|_{L_{2r}}\le\alpha\|X_{ij}\|_{L_r}
\qquad(1\le i,j\le n,\ r\ge1).$$

Set $[n]=\{1,\ldots,n\}$ and

$$
M(X)=\max_i\left(\sum_j\mathbb E X_{ij}^2\right)^{1/2}
+\max_j\left(\sum_i\mathbb E X_{ij}^2\right)^{1/2},
$$

$$
D(X)=\max_{1\le k\le n}\;
\min_{\substack{I\subseteq[n]\\|I|\le k}}
\sup_{\substack{s,t\in\mathbb R^n\\\|s\|_2,\|t\|_2\le1}}
\left\|\sum_{\substack{i\notin I\\j\notin I}}X_{ij}s_it_j
\right\|_{L_{\ln(k+1)}}.
$$

**Conjecture (Latała–Świątkowski).** For every $\alpha\ge1$ there is a
constant $C_\alpha>0$ such that, for every $n\ge1$ and every such matrix,

$$\mathbb E\|X\|_2\le C_\alpha\bigl(M(X)+D(X)\bigr),$$

where $\|X\|_2$ is the spectral norm. The constant is independent of the
dimension and entry laws. The same deterministic index set $I$ deletes both
rows and columns; the supremum is outside the random-variable moment.
The definition includes $L_{\ln2}$ when $k=1$, using the displayed moment
functional even though its exponent is below one.

The reverse inequality up to a constant depending only on $\alpha$ is
proved, so the target is equivalent to the source's two-sided comparison.
No identical-distribution or symmetry assumption is imposed on the entries.

## Known cases and numerical significance

The source proves the Gaussian-mixture case under the same moment condition.
Weighted signs $X_{ij}=a_{ij}\varepsilon_{ij}$, with independent fair
$\varepsilon_{ij}\in\{-1,1\}$, satisfy the condition with $\alpha=1$ and
form the source's earlier Conjecture 1.2. Latała proves this case when
$a_{ij}\in\{0,1\}$ and proves the general weighted-sign estimate with an
additional factor of order $\log\log\log n$. Meller's 2026 result gives
an iterated-logarithm loss for a wider class of symmetric entries; it does
not remove that loss. These cases remain grouped in this entry.

The spectral norm is the largest singular value and measures the largest
Euclidean amplification by a random matrix. The formula combines row and
column variance scales with moments of bilinear forms after deleting a
limited number of coordinates, accounting for concentration on small parts
of a matrix that simpler variance-only bounds can miss.

## References and status check

- R. Latała and W. Świątkowski, *Norms of randomized circulant matrices*, Electronic Journal of Probability 27 (2022), paper 80, 1–23. [DOI](https://doi.org/10.1214/22-EJP799); [current arXiv v2](https://arxiv.org/pdf/2106.03139v2), dated 2022-05-27. Conjecture 4.3 on preprint p.25, with condition (25) on p.24, states the target. Theorem 4.1 supplies the lower bound; Proposition 4.4 and the paragraph before it cover Gaussian mixtures. Conjecture 1.2 on p.2 is the weighted-sign special case.
- R. Latała, *On the spectral norm of Rademacher matrices*. [DOI](https://doi.org/10.1090/tran/9637); [current arXiv v2](https://arxiv.org/html/2405.13656v2), dated 2025-08-18. Equations (1.2)–(1.3), Theorem 1.1, and Theorem 1.9 give the weighted-sign conjecture and the stated partial results. This paper uses the comparable truncated logarithm $\max\{1,\ln k\}$ in place of $\ln(k+1)$.
- R. Meller, *Spectral norm of matrices with independent entries up to polyloglog*, [arXiv:2512.23673v2](https://arxiv.org/html/2512.23673v2), dated 2026-01-29, introduction, equation (3), and Theorem 1.1. It explicitly identifies the remaining logarithmic gap and Conjecture 4.3.

On 2026-09-11, checked the original paper's current version, both later
papers, and exact-title, author/conjecture, Rademacher spectral-norm,
proof/counterexample and 2026 searches. No full resolution was found.
Gaussian operator-norm results and the general Bernoulli-process theorem
do not prove this displayed formula. This is a bounded literature check.
