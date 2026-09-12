# SP-09 / SP-07: Exact orbit distance when one spectrum has two points

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.  
**Submission date:** 12 September 2026.  
**Editorial record:** [Attribution, independent review and scope](../README.md).

The review statements below describe the supplied draft; the linked submission record records subsequent independent review.

**Scope:** A complete analytical proof for normal pairs in which at least one
matrix has at most two distinct eigenvalues. This does **not** settle SP-09 for
general normal pairs or determine the universal constant in SP-07.

**Review and attribution:** Session-derived proof; no independent external or
formal verification. No novelty claim. In particular, the theorem may be a
known spectral-variation special case and requires a prior-art check before
submission as new progress.

## 1. Definitions

For normal matrices $`A,B\in\mathbb C^{n\times n}`$, let


```math
\delta_n(A,B)=\min_{U^*U=I}\|A-U^*BU\|_2
```


and let $`d_\infty(A,B)`$ be the minimum, over bijections between their
eigenvalue multisets, of the largest matched distance.

Suppose first that $`A`$ has distinct eigenvalues $`a,b`$, with multiplicities
$`p,n-p`$, where $`1\le p< n`$. List the eigenvalues of $`B`$ with multiplicity
as $`\beta_1,\ldots,\beta_n`$. For $`t\ge0`$, define


```math
N_a(t)=\#\{j:|\beta_j-a|\le t\},\qquad
N_b(t)=\#\{j:|\beta_j-b|\le t\}.
```



## 2. The exact formula

### Theorem 1

For these matrices,


```math
\delta_n(A,B)=d_\infty(A,B).
\tag{1}
```


Their common value is the least $`t\ge0`$ for which all three conditions hold:


```math
\begin{split}
&\min\{|\beta_j-a|,|\beta_j-b|\}\le t\quad\text{for every }j,\\
&N_a(t)\ge p,\\
&N_b(t)\ge n-p.
\end{split}
\tag{2}
```


Equivalently, writing $`r_a(p)`$ for the $`p`$-th smallest member of the
multiset $`\{|\beta_j-a|\}`$, and similarly for $`r_b(n-p)`$,


```math
\delta_n(A,B)=\max\left\{
\max_j\min(|\beta_j-a|,|\beta_j-b|),\ r_a(p),\ r_b(n-p)
\right\}.
\tag{3}
```



### Proof

Fix any normal representative $`C=U^*BU`$, and put $`t=\|A-C\|_2`$.
Let $`P`$ be the orthogonal projection onto the $`a`$-eigenspace of $`A`$,
so $`A=aP+b(I-P)`$ and $`\mathop{\mathrm{rank}}\nolimits P=p`$.

For a unit $`\beta_j`$-eigenvector $`v`$ of $`C`$, orthogonality of the two
summands gives


```math
\|(A-C)v\|^2
=|a-\beta_j|^2\|Pv\|^2+
|b-\beta_j|^2\|(I-P)v\|^2
\ge\min(|a-\beta_j|^2,|b-\beta_j|^2).
```


Hence the first condition in (2) is necessary.

Let $`L_a`$ be the spectral subspace of the normal matrix $`C`$ spanned by
its eigenvectors with $`|\beta_j-a|>t`$. If $`N_a(t)< p`$, then


```math
\dim L_a+\dim\mathop{\mathrm{ran}}\nolimits P=n-N_a(t)+p>n.
```


Choose a nonzero vector $`w\in L_a\cap\mathop{\mathrm{ran}}\nolimits P`$. Since
$`Aw=aw`$, and since the eigenvectors of $`C`$ form an orthonormal basis,


```math
\|(A-C)w\|=\|(aI-C)w\|>t\|w\|,
```


a contradiction. Therefore $`N_a(t)\ge p`$. Applying the same argument to
$`b`$ and $`I-P`$ proves the third condition. Strictness here is justified
because the finite collection of distances defining $`L_a`$ is strictly
greater than $`t`$; threshold equality is retained in $`N_a(t)`$.

Conversely, suppose (2) holds. Each eigenvalue of $`B`$ is within $`t`$ of at
least one of $`a,b`$. The number that is close only to $`a`$ is
$`n-N_b(t)\le p`$, and the number close only to $`b`$ is
$`n-N_a(t)\le n-p`$. Assign those eigenvalues to their forced sides. All
remaining eigenvalues are close to both points and can fill the remaining
capacities, which are nonnegative and have the correct total. This constructs
a bijection with maximum distance at most $`t`$.

Normal spectral decompositions allow that bijection to be realized by a unitary
alignment of orthonormal eigenbases. The difference of the resulting diagonal
matrices has operator norm equal to the largest matched distance. Consequently
$`\delta_n\le d_\infty`$. The necessary conditions already show
$`d_\infty\le\|A-U^*BU\|`$ for every $`U`$, giving the reverse inequality.
Formula (3) is exactly the threshold characterization (2). $`\square`$

For a scalar $`A=aI`$, the analogous result is immediate:
$`\delta_n(A,B)=\max_j|a-\beta_j|=d_\infty(A,B)`$. Symmetry in the two
orbits allows the two-point hypothesis to be imposed on either matrix.

## 3. Finite block repetition

### Corollary 2

If $`A,B`$ are normal and one has at most two distinct eigenvalues, then for
every positive integer $`k`$,


```math
\delta_{nk}(I_k\otimes A,I_k\otimes B)=\delta_n(A,B).
\tag{4}
```



**Proof.** In (2), repetition leaves the coverage condition unchanged and
multiplies both counts and both required multiplicities by $`k`$. Thus the
set of admissible thresholds is identical. Apply Theorem 1 in both dimensions.
The scalar case is immediate. $`\square`$

This is a subclass of the finite-normal amplification question. It includes
arbitrary multiplicities and non-real, non-collinear choices of the other
matrix's spectrum; it is not confined to self-adjoint pairs. It does not cover
pairs with at least three distinct eigenvalues on both sides.

## 4. Consequence for SP-07

Taking $`U=I`$ in the necessary half of Theorem 1 gives


```math
d_\infty(A,B)\le\|A-B\|_2
```


for the same two-point subclass. The constant one is sharp there: take
$`A=\mathop{\mathrm{diag}}\nolimits(0,1)`$ and $`B=A+\epsilon I`$, with
$`0<\epsilon<1/2`$. Both the matching distance and the norm difference are
$`\epsilon`$.

This is **not** an assertion that the all-normal constant is one. The pinned
SP-07 statement explicitly excludes that refuted general conjecture and asks
for the remaining sharp universal constant.

## 5. Sources and verification priorities

The exact targets are the SP-09 and SP-07 READMEs at commit
`f41f1f9ffa2171550d4bb795862c6170c4f26070`; provenance is in
`../sources/snapshot.json`. The repository cites Marcoux–Zhang (2021), Section 5,
and Marcoux–Sarkowicz–Zhang, arXiv:2508.13834v1, for SP-09 context.

The proof above is self-contained apart from the finite-dimensional spectral
theorem and the dimension inequality for intersections of subspaces. A reviewer
should check the strict-threshold step, the assignment sufficiency in (2), and
whether this standard-looking subclass is already in the literature before
proposing any catalog change.
