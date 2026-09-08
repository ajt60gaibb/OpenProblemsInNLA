# Nonnegative factorization: identifiability and global approximation

> Legacy source map and screening notes. Admitted statements have moved to category/problem folders. Follow the links below or [browse the new index](../../CATALOG.md). Shared notation and uncounted material are retained here as the historical source record.

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

[Open the problem folder](../../nonnegative-and-positive-factorizations/NM-01/README.md) · [PDF](../../nonnegative-and-positive-factorizations/NM-01/problem.pdf) · [LaTeX](../../nonnegative-and-positive-factorizations/NM-01/problem.tex)


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

[Open the problem folder](../../nonnegative-and-positive-factorizations/NM-03/README.md) · [PDF](../../nonnegative-and-positive-factorizations/NM-03/problem.pdf) · [LaTeX](../../nonnegative-and-positive-factorizations/NM-03/problem.tex)


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
