# AC-06 — Explicit tensors with quadratic border rank

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because explicit superlinear tensor lower bounds remain far below generic quadratic behavior; broad importance is the construction of hard instances for bilinear computation and circuit lower bounds.  
**Topic:** explicit lower bounds for tensor decompositions  
**Last checked:** 2026-11-26  
**Status:** Open  

## Context and notation

Over $`\mathbb C`$, the tensor rank $`R(T)`$ is the minimum number of pure tensors in an exact sum for $`T`$. The border rank $`\underline R_{\mathbb C}(T)`$ is the least $`r`$ such that $`T`$ is a Euclidean limit of complex tensors of rank at most $`r`$.

## Problem statement

Construct a deterministic algorithm that, on input the positive
integer $`n`$, outputs the rational entries of a tensor
$`T_n\in\mathbb Q^{n\times n\times n}`$ in time polynomial in $`n`$, and prove that
there are constants $`c>0,n_0`$ such that
$`\underline R_{\mathbb C}(T_n)\ge c n^2`$ for all $`n\ge n_0`$.
Output rationals are encoded by binary integer numerators and denominators;
thus the time bound also limits their bit lengths. Border rank is over $`\mathbb C`$, as defined in the notation.

## Why it matters

Explicit hard tensors would supply lower bounds for
bilinear computation that are much stronger than the currently available
examples. Generic existence does not provide the required efficient construction.

## Progress — explicit superlinear border rank

There is a polynomial-time family of $`0`$–$`1`$ tensors in
$`\mathbb Q^{n\times n\times n}`$ with complex border rank at least
$`\lfloor\sqrt n\rfloor^{9/4}=(1-O(n^{-1/2}))n^{9/8}`$.
Moreover, for every $`\varepsilon>0`$, sums of rectangular multiplication
blocks on disjoint coordinates with all three total factor dimensions at most
$`n`$ have border rank $`O_\varepsilon(n^{9/8+\varepsilon})`$.
Thus $`9/8`$ is the optimal exponent for this class of constructions.

Let $`M_{a,b,c}`$ be the matrix multiplication tensor with factor dimensions
$`ab,bc,ca`$, using the cyclic form

```math
M_{a,b,c}=\sum_{i=1}^a\sum_{j=1}^b\sum_{k=1}^c
  e_{ij}\otimes e_{jk}\otimes e_{ki}.
```

Corollary 1.2 of OpenAI's November preprint gives
$`\underline R_{\mathbb C}(M_{q,q,q})\ge q^{9/4}`$ for $`q\ge2`$ and
$`\widetilde R(M_{q,q,q})=q^{9/4}`$, where $`\widetilde R`$ is asymptotic
rank over $`\mathbb C`$. The rank-at-most-$`r`$ locus is the image of the
polynomial map that sums $`r`$ pure tensors. It is constructible, so its
Zariski and Euclidean closures over $`\mathbb C`$ coincide.
[Preprint, Corollary 1.2](https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf) ·
[Carlos Toledo's formal audit, G3c and G3d](https://carlostoledo.co/omega/).

### Construction

Given $`n`$, set $`q=\lfloor\sqrt n\rfloor`$. Identify each first
$`q^2`$-dimensional coordinate block with the pairs in $`\{1,\ldots,q\}^2`$,
and put $`M_{q,q,q}`$ in the product of those three blocks. On the
remaining coordinates, add $`e_\ell\otimes e_\ell\otimes e_\ell`$ for each
$`q^2<\ell\le n`$, using $`e_\ell`$ for the individual coordinate vectors.
All other entries are zero. To test a coefficient, decode the coordinate
pairs and compare the repeated indices in the cyclic formula, or test
for a diagonal entry on the remaining coordinates. This takes
$`O(n^3\mathop{\mathrm{polylog}}\nolimits(n+1))`$ bit operations for the
dense output, with numerator–denominator pairs $`(0,1)`$ and $`(1,1)`$.

Each added diagonal term is a scalar multiplication block, so the
family belongs to the class in the upper bound below. Each matrix
flattening has rank $`n`$, since its rows have nonempty disjoint
supports. Projection onto the first $`q^2`$ coordinates in each
factor recovers $`M_{q,q,q}`$. Linear maps on the
factors preserve limits and send a rank-one term to a term of rank at most
one. This proves the bound, including $`q=1`$, when the square block has
rank one.

### Upper bound for rectangular block sums

Fix $`\varepsilon>0`$. There is a power $`d=2^h`$, $`h\ge1`$, with
$`R(M_{d,d,d})\le d^{9/4+2\varepsilon}`$. The $`h`$-th Kronecker power
of $`M_{2,2,2}`$ is $`M_{2^h,2^h,2^h}`$ up to reindexing, and its
rank to the power $`1/h`$ tends to $`2^{9/4}`$. For any integer $`c\ge1`$, take the
least $`j\ge0`$ with $`d^j\ge c`$. Restriction from size $`d^j`$ and
submultiplicativity of rank under Kronecker products give
$`R(M_{c,c,c})\le K_\varepsilon c^{9/4+2\varepsilon}`$, with
$`K_\varepsilon=d^{9/4+2\varepsilon}`$.

Permuting the factors and, when needed, reversing the coordinate pairs
in the bases lets us assume
$`a\ge b\ge c`$. Partition the first two index sets into groups
of size at most $`c`$. Each pair of groups contributes a restriction of
one copy of $`M_{c,c,c}`$, so

```math
R(M_{a,b,c})
\le \lceil a/c\rceil\lceil b/c\rceil R(M_{c,c,c})
\le 4K_\varepsilon ab\,c^{1/4+2\varepsilon}
\le 4K_\varepsilon (ab)^{9/8+\varepsilon}.
```

The last inequality uses $`c^2\le ab`$. For a direct sum of such blocks,
let $`s_j`$ be the largest factor dimension of block $`j`$. The three
aggregate dimension bounds imply $`\sum_j s_j\le3n`$. Summing the rank
bounds gives at most $`4K_\varepsilon(3n)^{9/8+\varepsilon}`$ since the
exponent is greater than one. Factorwise linear images of these sums in
the $`n\times n\times n`$ format inherit the bound. Their limits also inherit
it because each border-rank sublevel set is closed.

The original target is still a quadratic lower bound for a polynomial-time
rational family.

## References and status

M. Michałek and J. Landsberg,
[*Towards Finding Hay in a Haystack: Explicit Tensors of Border Rank Greater
Than 2.02m*](https://www.theoryofcomputing.org/articles/v021a013/v021a013.pdf),
Theory of Computing 21(13), 2025, §1 and Definition 1.1, distinguishes
polynomial-time explicitness from weaker notions and obtains a linear bound.
The quadratic target and rational-output encoding are an editorial quantitative
formulation of the paper's explicit-versus-generic challenge, not a numbered
conjecture quoted from it.

Benjamin Lovitz's October preprint gives a deterministic polynomial-time
integer construction with border rank at least $`3n-11n^{3/4}`$.
[Preprint, Theorem 1.1](https://arxiv.org/html/2610.08504v1).

## Status check — 2026-09-10

Rechecked the [2025 Landsberg–Michałek paper](https://www.theoryofcomputing.org/articles/v021a013/v021a013.pdf), and searched for explicit superlinear or quadratic border-rank constructions. The July 2026 [Arithmetic circuit lower bounds from sumset expansion](https://arxiv.org/abs/2607.15848), also [ECCC TR26-138](https://eccc.weizmann.ac.il/report/2026/138/), gives semi-explicit tensors over number fields. That does not meet the displayed polynomial-time rational-output requirement. No qualifying quadratic construction was located.

## Reviewed research submission — 14 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation and submission record](../../references/holden-ac-2026-09-14/README.md).

Theorems 2.1–5.3 prove compaction, conditional reductions and a scoped method ceiling. Section 6 supplies finite certificates for dimensions 2–9. A polynomial-time detecting family and all-dimension quadratic lower bound remain missing.

**Status: Open.** [Report](../../references/holden-ac-2026-09-14/AC-06-submission.pdf) · [Independent AI-agent audit and limitations](../../references/holden-ac-2026-09-14/verification/review-ac05-ac06.md). AI assistance disclosed; no external human review, formal verification or Lean checks. Original target and prior-source credit retained.
