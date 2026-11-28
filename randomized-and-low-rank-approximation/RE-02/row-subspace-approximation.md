# Depth-independent queries for prescribed row subspaces

Use the HSS class and benchmark $`E_{L,k}(A)`$ from [RE-02](README.md).
Fix an integer $`a\ge1`$. For each $`(L,k)`$ prescribe subspaces
$`V_i\subseteq\mathbb R^N`$ of dimensions $`d_i\le ak`$ for
$`1\le i\le N`$. Assume orthonormal bases of the subspaces can be
computed from $`(L,k)`$ in polynomial time. Let $`\mathcal V`$ consist
of matrices whose transposed rows belong to the corresponding $`V_i`$.

There is a polynomial-time randomized algorithm that uses
$`q=2ak+2`$ forward matrix–vector queries and returns
$`B\in\mathcal S_{L,k}`$. For every fixed $`M\ge0`$ its guarantee is

```math
\operatorname{dist}_F(A,\mathcal V)^2\le M E_{L,k}(A)
\quad\Longrightarrow\quad
\mathbb E\|A-B\|_F^2\le (20M+8)L\,E_{L,k}(A).
```

When $`\mathcal V\subseteq\mathcal S_{L,k}`$, the same sketches
give a variant with squared error at most $`2M E_{L,k}(A)`$.

## Recovering the projected rows

Query $`Y=A\Omega`$ for an $`N\times q`$ matrix $`\Omega`$ with
independent standard Gaussian entries. For the $`i`$th row, let
$`U_i`$ have orthonormal columns spanning $`V_i`$. Decompose its
transpose as $`U_i c_i+r_i`$, where $`r_i\perp V_i`$. Then

```math
Y_{i,:}^{\mathsf T}=G_i^{\mathsf T}c_i+\Omega^{\mathsf T}r_i,
\qquad G_i=U_i^{\mathsf T}\Omega.
```

$`G_i`$ is standard Gaussian of size $`d_i\times q`$. The noise
$`\Omega^{\mathsf T}r_i`$ is independent of $`G_i`$ with covariance
$`\|r_i\|_2^2 I_q`$, by orthogonality. Use least squares to estimate
$`c_i`$ from $`Y_{i,:}`$ and set the transposed row of $`\widehat A`$
to $`U_i\widehat c_i`$. For $`d_i=0`$ the estimated row is zero.
The algorithm can also set the estimated row to zero on the
probability-zero event of a rank-deficient design.

Conditionally on $`G_i`$, the mean squared coefficient error is
$`\|r_i\|_2^2\operatorname{tr}((G_iG_i^{\mathsf T})^{-1})`$.
Each diagonal of the inverse is, by the Schur complement, the
reciprocal squared length of the corresponding Gaussian row after
orthogonal projection away from the other $`d_i-1`$ rows. Its
expectation is $`1/(q-d_i-1)`$, the reciprocal-mean identity obtained
by integrating the chi-square density with $`q-d_i+1`$ degrees of
freedom. Using $`r_i\perp V_i`$ and adding over the rows gives

```math
\mathbb E\|\widehat A-A\|_F^2
=\sum_{i=1}^N
  \left(1+\frac{d_i}{q-d_i-1}\right)\|r_i\|_2^2
\le 2\operatorname{dist}_F(A,\mathcal V)^2 .
```

The estimates can share the same $`\Omega`$ because only the
expectation of each row's squared error enters this sum.

## Rank-constrained output

If $`\mathcal V\subseteq\mathcal S_{L,k}`$, return $`\widehat A`$.
Otherwise, apply the explicit-entry version of Algorithm 1 of
[Amsel et al., Section 3 and Theorem 6](https://arxiv.org/html/2505.16937v2#S3)
to $`\widehat A`$. It returns $`B\in\mathcal S_{L,k}`$ and satisfies
$`\|\widehat A-B\|_F^2\le 2L E_{L,k}(\widehat A)`$.
Writing $`D=\|\widehat A-A\|_F^2`$ and using an optimal HSS
approximation to $`A`$ as a comparator gives
$`E_{L,k}(\widehat A)\le 2D+2E_{L,k}(A)`$. Consequently

```math
\|A-B\|_F^2\le (2+8L)D+8L E_{L,k}(A).
```

Taking expectations and using $`L\ge1`$ proves the guarantee.
The query cap is deterministic and the least-squares solves and
explicit-entry HSS approximation require polynomially many operations.

## Examples of the promise

- If some closest HSS approximation is supported on a prescribed
  pattern with at most $`ak`$ entries per row, take $`V_i`$ to be the
  corresponding coordinate subspace. Then the promise holds with
  $`M=1`$, with no sparsity restriction on $`A`$.
- Fix a prescribed $`k`$-dimensional subspace $`V`$ with basis matrix
  $`U`$. For row $`i`$ in leaf $`I`$, take $`V_i=V+\mathbb R^I`$,
  with $`\mathbb R^I`$ denoting the coordinate subspace on $`I`$.
  These subspaces have dimension at most $`3k`$. Every matrix in
  $`\mathcal V`$ has the form $`D+XU^{\mathsf T}`$, with $`D`$ leaf
  block diagonal. Every nonroot off-diagonal block has rank at most
  $`k`$, so $`\mathcal V\subseteq\mathcal S_{L,k}`$. On inputs whose
  nearest HSS approximation has this form, the algorithm achieves a
  factor of two directly.

## A lower bound for the general query model

Any randomized algorithm satisfying RE-02, including adaptive algorithms
using both forward and transpose products, requires at least $`3k`$
queries in the worst case. Choose the set $`T`$ consisting of a full leaf
and any $`k`$ coordinates in its sibling. Every real matrix supported on
$`T\times T`$ is HSS of rank at most $`k`$. The only nonzero cuts are at
the two sibling leaves, and each of their cross blocks has a side of
size at most $`k`$.

Put a standard Gaussian matrix on the $`3k\times3k`$ block and fix any
value of the algorithm's random coins. Given a query transcript, the
conditional law of the Gaussian block is Gaussian on an affine
subspace. Its direction space consists of the matrices that annihilate
the span $`F`$ of the forward query inputs restricted to $`T`$, with
transposes that annihilate the analogous span $`G`$ for transpose
queries. This statement follows by induction, conditioning at each step
on a linear map that is fixed given the previous transcript. The
direction space has dimension
$`(3k-\dim F)(3k-\dim G)`$. Fewer than $`3k`$ total queries leave it
positive-dimensional, so the conditional law assigns zero probability
to any single output block. The probability of exact recovery is
therefore zero under this Gaussian prior, also after averaging over the
algorithm's coins. But zero benchmark error forces exact recovery almost
surely on every fixed HSS input, which would give probability one under
the same prior.
