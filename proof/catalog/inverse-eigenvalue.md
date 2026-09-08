# Inverse spectra and structured conditioning

Five admitted problems. Difficulty and importance are editorial assessments.
All status searches below were performed on **2026-09-08**. “Open” means that
the cited source poses the question and the recorded searches found no complete
resolution; it is a bounded literature assessment.

<a id="is-01"></a>

## IS-01 — Two permutation matrices generate the doubly stochastic spectral boundary

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open.

Let $\mathcal D_n$ consist of the real entrywise-nonnegative $n\times n$
matrices whose row and column sums are all one, and define the single-eigenvalue
region

$$
D_n=\{z\in\mathbb C:z\in\sigma(A)\text{ for some }A\in\mathcal D_n\}.
$$

Prove or disprove that, for every integer $n\geq1$ and every
$z\in\partial D_n$, there exist $n\times n$ permutation matrices $P,Q$
and $t\in[0,1]$ such that

$$
\det\bigl(zI-tP-(1-t)Q\bigr)=0.
$$

The boundary is taken in the usual topology of $\mathbb C$, and $P=Q$
is allowed. The task concerns one eigenvalue, not simultaneous realization of
a prescribed full spectrum. It would reduce boundary computation to a finite
collection of one-parameter matrix families. Counterexamples for convex hulls
of other matrix groups do not automatically apply to all permutation matrices.

**References:** Harlev, Johnson, and Lim, [*The Doubly Stochastic Single
Eigenvalue Problem: A Computational Approach*](https://arxiv.org/html/1908.03647v2),
Conjecture 2.7 and §6; published in *Experimental Mathematics* 31 (2022),
936–945. Verbeken and Ginis, [ILAS 2026 abstract](https://ilas2026.math.vt.edu/docs/ILAS2026-Book-Of-Abstracts.pdf),
p. 150.

**Status check:** Searches for `Harlev Johnson Lim boundary conjecture` and
`doubly stochastic boundary conjecture 2026` found the 2026 authors reporting
numerical support through order 25, rather than a proof. The older
Perfect–Mirsky conjecture fails at order five; that failure does not refute
this different assertion.

<a id="is-02"></a>

## IS-02 — Where a symmetric stochastic matrix can be spectrally unique

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** open.

For $n\geq4$, put
$\mathcal S_n=\{A\in\mathbb R^{n\times n}:A=A^T,\ A\geq0,\ A\mathbf1=\mathbf1\}$
and $C_n=(\mathbf1\mathbf1^T-I)/(n-1)$. A matrix $A\in\mathcal S_n$
is *spectrally unique* if every $B\in\mathcal S_n$ with the same eigenvalues,
including multiplicities, satisfies $B=R^TAR$ for a permutation matrix $R$.
Let $[X,Y]=\{(1-t)X+tY:0\leq t\leq1\}$.

Prove or disprove the following necessary condition: every spectrally unique
$A\in\mathcal S_n$ with $\operatorname{tr}A>0$ belongs to

$$
[I,C_n]\ \cup\!
\bigcup_{V\in\operatorname{vert}(\mathcal S_n)}
\bigl([I,V]\cup[C_n,V]\bigr).
$$

Here a vertex is an extreme point of the indicated convex polytope; it need
not be a permutation matrix. Only the stated implication is asserted.
This asks where recovering a nonnegative symmetric stochastic matrix from its
spectrum can be unique up to relabeling, a different issue from mere spectral
feasibility.

**References:** Mourad and Abbas, [2013 preprint](https://arxiv.org/pdf/1310.1273),
definitions in §1 and Conjecture 5.1, p. 10;
[published article](https://doi.org/10.1080/03081087.2014.903590),
*Linear and Multilinear Algebra* 63 (2015), 869–881.

**Status check:** Searches for the exact title, `symmetric doubly stochastic
Conjecture 5.1`, and author/title combinations with `counterexample` and
`2026` found no resolution. The source solves order three, which is excluded
from the remaining statement above.

<a id="is-03"></a>

## IS-03 — Johnson's derivative-realizability conjecture

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open.

For every integer $n\geq5$ and every real entrywise-nonnegative matrix
$A\in\mathbb R^{n\times n}$, define $p_A(z)=\det(zI-A)$.
Must there exist an entrywise-nonnegative
$B\in\mathbb R^{(n-1)\times(n-1)}$ such that

$$
\det(zI-B)=\frac1n p_A'(z)\qquad\text{as polynomials in }z?
$$

Equivalently, the critical points of the characteristic polynomial, counted
with multiplicity, would themselves form a realizable spectrum of the smaller
order. Neither $A$ nor $B$ is assumed symmetric or diagonalizable. The
realization must have exactly order $n-1$; allowing arbitrary additional zero
eigenvalues changes the problem. This would provide a dimension-reduction
operation for nonnegative spectral realization.

**References:** Hoover, McCormick, Paparella, and Thrall,
[*On the realizability of the critical points of a realizable list*](https://arxiv.org/pdf/1712.05454),
Conjecture 1.2, p. 2, and §6. The paper credits the conjecture to Johnson and
records the Cronin–Laffey low-order results.

**Status check:** Searches for `Johnson conjecture derivative nonnegative
matrix characteristic polynomial proof counterexample`, `1712.05454 2026`,
and `Monov conjecture solved` found no general resolution. The source proves
several classes and records the solved cases $n\leq4$, and
$n\leq6$ with $\operatorname{tr}A=0$. Nonnegative power sums alone are a
different hypothesis. Monov's weaker moment conjecture is not separately
counted here.

<a id="is-04"></a>

## IS-04 — A condition number of two for a sign matrix in every dimension

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open.

For $n\geq1$, define

$$
h(n)=\min_{A\in\{-1,1\}^{n\times n}}\kappa_2(A),\qquad
\kappa_2(A)=\frac{\sigma_{\max}(A)}{\sigma_{\min}(A)},
$$

with $\kappa_2(A)=+\infty$ for singular $A$. Prove or disprove

$$
\sup_{n\geq1}h(n)=2.
$$

Since $h(3)=2$, the unresolved claim is the upper bound in every dimension.
No symmetry or circulant structure is imposed. The target refines the known
existence of uniformly well-conditioned sign matrices, which is useful for
constructing approximately isometric linear maps and well-conditioned bases.

**References:** Alexeev, Jasper, and Mixon,
[*Asymptotically optimal approximate Hadamard matrices*](https://arxiv.org/html/2511.14653v1),
§6, Problem 12. Dong and Rudelson,
[*Approximately Hadamard matrices and Riesz bases in random frames*](https://arxiv.org/abs/2207.07523),
introduction; *IMRN* (2024), 2044–2065.

**Status check:** Searches for `approximate Hadamard sup 2 conjecture`,
`2511.14653 2026 condition number`, and `approximate Hadamard supremum`
found no proof of the sharp constant. The fact that $h(n)\to1$ is already
known and is not the problem counted here.

<a id="is-05"></a>

## IS-05 — The optimal decay exponent for the conditioning of sign matrices

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** open.

With $h(n)$ defined in IS-04, determine the exact number

$$
\alpha_*=\sup\{\alpha\geq0:\ \exists C>0\ \forall n\geq1,
\ h(n)-1\leq Cn^{-\alpha}\}.
$$

The constant $C$ may depend on $\alpha$, but not on dimension. This
specifies the uniform asymptotic power exponent; logarithmic factors do not
change the supremum. Orders admitting exact Hadamard matrices have
$h(n)-1=0$, which are included without taking logarithms of zero.
Current bounds give $17/92\leq\alpha_*\leq1$.

**References:** Alexeev, Jasper, and Mixon,
[*Asymptotically optimal approximate Hadamard matrices*](https://arxiv.org/html/2511.14653v1),
§6, Problem 11; the supremum above is an editorial precise formulation of
its decay-exponent question. Steinerberger,
[*Open Problems*](https://faculty.washington.edu/steinerb/openproblems.pdf),
Problem 69, November 2025 update, identifies the sharp rate as unresolved.

**Status check:** Searches for `approximate Hadamard 17/92 2026` and
`approximate Hadamard condition 2026 sharp` found no exact exponent. A global
constant as in IS-04 does not specify a decay exponent, while an asymptotic
exponent permits finitely many exceptions to any proposed sharp constant.
The two independently posed problems are therefore retained separately.

## Withheld leads and resolved questions — not included in the count

- **Order-four symmetric stochastic spectral feasibility:** the revised
  Kaddoura–Mourad conjecture, still described as open by
  [Jung and Kim (2024)](https://doi.org/10.1515/math-2023-0176), is excluded
  following Benjamin James Clark's 2026 dissertation,
  [*The Nonnegative Inverse Eigenvalue Problem: A Theoretical and Computational
  Investigation*](https://rex.libraries.wsu.edu/esploro/outputs/doctoral/The-Nonnegative-Inverse-Eigenvalue-Problem-A/99901393504301842),
  Chapter 3, Theorem 3.0.1. The dissertation claims the necessary-and-sufficient
  criterion $\sum_i\lambda_i\geq0$ and
  $(1+\lambda_3)(1+\lambda_4)+(\lambda_2+\lambda_3)(\lambda_2+\lambda_4)\geq0$
  for $1=\lambda_1\geq\lambda_2\geq\lambda_3\geq\lambda_4\geq-1$.
- **Residual symmetric NIEP of order five:**
  [Jin, Ke, and Sui (August 2026)](https://arxiv.org/html/2608.19435v1),
  Equations (3)–(4) and §5, explicitly leave the region
  $\mathcal R\setminus\mathcal W$ unclassified. Their new impossibility
  region must be removed from any historical formulation. This remains a
  strong source lead; merely asking whether a quantifier-free feasibility
  criterion exists would restate what real quantifier elimination already
  guarantees, rather than specify the missing classification.
- **Uniform real orthogonal coherence with a prescribed constant column:**
  [Kania (2025)](https://arxiv.org/html/2509.24079v1), Lemma 9 and §6, asks for
  an $\varepsilon>0$ and orthogonal matrices $Q_n$ for every $n$, with
  first column $\mathbf1/\sqrt n$ and
  $n\max_{1\leq i\leq n,\,2\leq j\leq n}|(Q_n)_{ij}|^2\leq2-\varepsilon$.
  Withheld pending comparison with the later flat-orthogonal construction in
  Alexeev–Jasper–Mixon, §2. The prescribed column is a material constraint;
  neither current openness nor a resolution is asserted here.
- **Every normalized realizable-spectrum boundary point is radially
  extremal:** [Johnson and Paparella](https://arxiv.org/html/2409.07682v2),
  Conjecture 9.2, is withheld because the boundary's ambient topology needs
  clarification. Normalized spectra of real matrices occupy a constrained
  subset of $\mathbb C^n$; counting its ordinary ambient boundary is not
  interchangeable with a relative boundary in a spectral parameter space.
- **Totally extremal ideal Perron similarities:** excluded following
  [Artemis and Paparella (June 2026)](https://arxiv.org/abs/2606.02865), which
  resolves the character-table conjecture from the preceding literature.
