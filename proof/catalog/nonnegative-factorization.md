# Nonnegative factorization: identifiability and global approximation

This chapter contains **2 admitted problems**. The literature checks below were performed on **2026-09-08**. They support
provisional open status; they are not an exhaustive proof that no solution
exists. Difficulty and importance are editorial assessments.

## Minimum-volume notation

For $H\in\mathbb R_+^{r\times n}$, let
$\operatorname{cone}(H)=\{Hy:y\in\mathbb R_+^n\}$ and let $e_d$ be the
all-ones vector in $\mathbb R^d$. Throughout NM-01 and NM-02, **SSC** means
the precise version in Gillis's Definition 4.15:

$$
\mathcal C_r=\{x\in\mathbb R_+^r:
e_r^Tx\geq\sqrt{r-1}\|x\|_2\}\subseteq\operatorname{cone}(H),
$$

and every orthogonal $Q\in\mathbb R^{r\times r}$ satisfying
$\operatorname{cone}(H)\subseteq\operatorname{cone}(Q)$ is a permutation
matrix. Some later sources use a stronger second condition involving the
boundary of the dual cone; that condition is not substituted here.

For $X\in\mathbb R^{m\times n}$ and $r=\operatorname{rank}(X)$, the
minimum-volume problem considered here is

$$
\min_{W\in\mathbb R^{m\times r},\ H\in\mathbb R_+^{r\times n}}
\det(W^TW)
\quad\text{subject to}\quad
X=WH,\qquad e_r^TH=e_n^T.\tag{MV}
$$

In particular, $W$ is unrestricted in sign and the **columns** of $H$ sum
to one. This is min-vol NMF (1), Definition 4.42 of the book.

<a id="nm-01"></a>

## NM-01 — Polynomial-time minimum-volume decision under sufficient scattering

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Topic:** structured matrix factorization; global optimization

Consider the following rational-input decision version of minimum-volume
optimization. The input is $X\in\mathbb Q^{m\times n}$, an integer
$2\leq r\leq\min(m,n)$, and $\tau\in\mathbb Q_{\geq0}$, with the promise
that $\operatorname{rank}(X)=r$ and that there exist real factors
$X=W_\star H_\star$ feasible for (MV) with $H_\star$ satisfying SSC.
These factors are not supplied. Decide whether

$$
\exists W\in\mathbb R^{m\times r},\ H\in\mathbb R_+^{r\times n}:
\quad X=WH,\quad e_r^TH=e_n^T,\quad\det(W^TW)\leq\tau.
$$

Does a polynomial-time algorithm exist, with time measured in the total
binary input length? Randomization is allowed with success probability at
least $2/3$ on every promised input. The algorithm must run in polynomial
time on all inputs but need only answer correctly on promised inputs.
Checking the SSC promise is not part of the task. This decision formulation
fixes the computational model of the book's polynomial-solvability
conjecture; it does not assert an equivalence with exact factor recovery.

**References:** Gillis, [*Nonnegative Matrix Factorization*](https://doi.org/10.1137/1.9781611976410),
§4.3.3.6, pp. 148–149, with Definitions 4.15 and 4.42 and Theorem 4.43;
[author-hosted book](https://orbi.umons.ac.be/bitstream/20.500.12907/42337/1/NMFbook_SIAM_reprint.pdf).
Barbarino, Gillis, and Saha,
[*Robustness of Minimum-Volume Nonnegative Matrix Factorization under an Expanded Sufficiently Scattered Condition*](https://arxiv.org/html/2511.04291v1),
§5, final research question.

**Status check:** Searches for `minimum-volume NMF polynomial time
sufficiently scattered` and `minimum volume simplex sufficiently scattered
algorithm 2026 2025` found no polynomial-time guarantee for this promise.
The November 2025 paper still asks for complexity results under its stronger
$p$-SSC assumption. Its robustness theorems assume a globally optimal
minimum-volume solution; they do not compute one in polynomial time.
The book explains why the maximum-inscribed-ellipsoid approach can require
exponentially many polytope facets.

<a id="nm-02"></a>

## Uncounted candidate NM-02 — Is sufficient scattering necessary for unique minimum-volume factors?

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Topic:** factorization identifiability; simplex geometry

**Admission withheld:** the source conjecture is precise, but a concrete
contrary geometric lead needs checking before it can be labeled open. A
[2021 MathOverflow answer](https://mathoverflow.net/questions/407397/least-area-and-least-perimeter-triangles-that-contain-a-convex-planar-region-h) claims a unique
minimum-area enclosing triangle for a specified quadrilateral. Its compatibility
with SSC after simplex-coordinate conversion has not been verified. This
is neither a confirmed refutation nor a cleared status check; NM-02 does not
count toward the collection.

For every $m,n,r$ with $2\leq r\leq\min(m,n)$, let
$X\in\mathbb R^{m\times n}$ have rank $r$. Suppose (MV) has a global
minimizer $(W_\star,H_\star)$ and its complete set of global minimizers is

$$
\{(W_\star P,P^TH_\star):
P\in\mathbb R^{r\times r}\text{ is a permutation matrix}\}.
$$

Must $H_\star$ satisfy SSC as defined above? Prove this implication or
give a counterexample. The hypothesis concerns uniqueness among **global
minimum-volume** factorizations, not uniqueness among all exact
factorizations and not uniqueness of a stationary point.

The converse implication is known: sufficient scattering identifies the
minimum-volume factors, up to permutation, under the stated rank and
normalization assumptions. Thus the question asks whether this geometric
condition exactly describes identifiability for the unconstrained-$W$
model. Adding $W\geq0$ changes the problem: the book already supplies a
counterexample to the corresponding necessity assertion.

**References:** Gillis, [*Nonnegative Matrix Factorization*](https://doi.org/10.1137/1.9781611976410),
§4.3.3.7, p. 149; Definition 4.15, Theorem 4.43, and the warning concerning
equation (4.18). Fu, Huang, Sidiropoulos, and Ma,
[*Nonnegative Matrix Factorization for Signal and Data Analytics*](https://arxiv.org/abs/1803.01257v4),
Definition 3, §V.B, and §VIII's final open-question bullet, manuscript p. 17
(IEEE Signal Processing Magazine 36(2), 59–80, 2019).

**Status check:** Searches for `VolMin conjecture necessary sufficiently
scattered`, `sufficiently scattered necessary unique minimum volume`, and
the same terms with `2025` and `2026` found no proof or refutation of this
specific necessity conjecture. Gillis and Luce's
[2024 SSC-checking paper](https://arxiv.org/html/2402.06019v1), §2,
explicitly distinguishes the book's orthogonal-cone condition from stronger
SSC variants. Vu Thanh and Gillis's
[2026 maximum-volume paper](https://arxiv.org/html/2602.04795v2), §II.C,
proves a sufficient-identifiability result for a related model; it does not
establish this converse.

<a id="nm-03"></a>

## NM-03 — Complexity of globally optimal nonnegative rank-two approximation

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Topic:** low-rank approximation; computational complexity

Given an arbitrary $X\in\mathbb Q_+^{m\times n}$ and
$\tau\in\mathbb Q_{\geq0}$, determine the complexity of deciding whether

$$
\exists W\in\mathbb R_+^{m\times2},\ H\in\mathbb R_+^{2\times n}:
\quad\sum_{i=1}^m\sum_{j=1}^n
\left(X_{ij}-\sum_{k=1}^2W_{ik}H_{kj}\right)^2\leq\tau.
$$

In particular, is there a deterministic algorithm polynomial in the total
binary input length, or is this decision problem NP-hard under polynomial-time
many-one reductions? This is a complexity-classification question, without
an assumption that these two outcomes exhaust the possibilities. The
factors may have real entries; only the data and threshold must be rational.
Their inner dimension is at most two, with a zero factor column permitted.

This fixes an exact decision interpretation of the literature's global
rank-two NMF optimization question. There is no promise that $X$ itself
has rank two. When a rank-two truncated SVD of $X$ is nonnegative, a best
nonnegative rank-two approximation is obtainable from it. Arbitrary input
can fall outside this tractable special case, and alternating nonnegative
least squares need not find a global optimum.

**References:** Gillis, [*Nonnegative Matrix Factorization*](https://doi.org/10.1137/1.9781611976410.ch6),
§6.1.3, p. 199, Theorem 6.6 and final paragraph. Lindy, Noferini, and
Van Dooren, [*On rank-2 Nonnegative Matrix Factorizations and their variants*](https://arxiv.org/abs/2507.20612v1),
§1, with §3's suboptimal approximation and §4's ANLS initialization.

**Status check:** Searches for `rank two nonnegative matrix factorization
approximation NP hard polynomial time 2025 2026` and `rank-2 NMF complexity
2026` found no resolution. The July 2025 primary paper explicitly identifies
rank two as an unresolved complexity case; its contribution is an effective
initial approximation and heuristic refinement. The March 2026
[constrained nonnegative Gram-feasibility preprint](https://arxiv.org/abs/2603.19976)
concerns partially specified symmetric matrices with affine side constraints,
which are absent from the problem above.

## Related directions — uncounted

- **Fixed-rank approximation in general.** Gillis §6.1.4, pp. 199–200, asks
  whether Frobenius NMF can be globally optimized in polynomial time for
  fixed factorization rank. NM-03 records the rank-two case explicitly
  singled out in both the book and subsequent research. The broader question
  is retained as a source lead, not an additional overlapping entry. General
  NMF hardness with rank as part of the input must not be misreported as a
  hardness theorem for every fixed rank $r\geq3$.
- **Noise robustness of minimum-volume NMF.** The broad historical direction
  in Gillis §4.3.3.6 has substantial new answers in Barbarino–Gillis–Saha
  (2025), Theorems 1–2. It should not be copied from the book as wholly
  unanswered. The quantitative sharpness questions in that paper require
  separate statements and checking.
- **Normalized maximum-volume identifiability.** Vu Thanh–Gillis (2026),
  §IV and §VI, asks about identifiability of normalized MaxVol NMF.
  The text does not specify a complete conjectured set of sufficient
  assumptions and equivalences, so it is retained as a lead.
