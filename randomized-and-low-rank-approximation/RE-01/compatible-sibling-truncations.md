# Exact HSS approximation when sibling truncations are compatible

Use the balanced binary tree, output class $`\mathcal S_{L,k}`$, and
error $`E_{L,k}`$ from [RE-01](README.md). Leave all diagonal leaf
blocks of $`A`$ unchanged. For each ordered pair $`(I,J)`$ of siblings,
take an optimal rank-at-most-$`k`$ truncated SVD of $`A[I,J]`$ in Frobenius
norm. Assemble these matrices into $`B_{\mathrm{sep}}`$ and test its
HSS cut ranks. If the test passes, $`B_{\mathrm{sep}}`$ is an exact
best HSS approximation. This gives an exact polynomial-time algorithm
on this subclass, with the rank and depth unrestricted.

## Proof

The diagonal leaf blocks and ordered sibling rectangles are disjoint
and partition the matrix. For distinct leaves, the least common
ancestor of their nodes determines the unique ordered sibling rectangle
containing their corresponding row and column indices.

Every $`B\in\mathcal S_{L,k}`$ has rank at most $`k`$ on each ordered
sibling rectangle, because $`B[I,J]`$ is a column submatrix of
$`B[I,I^c]`$. The Eckart–Young theorem therefore gives

```math
E_{L,k}(A)\ \ge\
\sum_{\text{ordered siblings }(I,J)}
     \sum_{j>k}\sigma_j(A[I,J])^2 .
```

By construction the error of $`B_{\mathrm{sep}}`$ equals this lower
bound. Passing the cut-rank tests makes it feasible and proves equality.
Taking all truncated SVDs and checking the ranks of the finitely many
cuts are polynomial-time operations in the stated model. If some
singular values tie at the truncation point, any particular selection
that passes the rank tests certifies optimality. If every block either
has rank at most $`k`$ or has a strict gap after its $`k`$th singular
value, the truncations are unique. At depth one every input passes.

## A family of inputs with full-rank sibling blocks

Choose any $`B_0\in\mathcal S_{L,k}`$ whose ordered sibling blocks all
have rank exactly $`k`$. For example, use $`B_0=UV^{\mathsf T}`$ where
$`U,V`$ have $`k`$ columns and their restrictions to every leaf have
full column rank. On each ordered sibling pair write a compact SVD
$`B_0[I,J]=U_{IJ}\Sigma_{IJ}V_{IJ}^{\mathsf T}`$ and add any perturbation
$`R_{IJ}`$ satisfying

```math
U_{IJ}^{\mathsf T}R_{IJ}=0,\qquad
R_{IJ}V_{IJ}=0,\qquad
\|R_{IJ}\|_2<\sigma_k(B_0[I,J]).
```

The perturbation acts between the two orthogonal complements of the
singular subspaces. The resulting block has its top $`k`$ singular
components exactly those of $`B_0[I,J]`$. The perturbations can be
chosen independently and of full rank on the complements, making every
sibling block of the input full rank. The diagonal leaf blocks are
arbitrary. The algorithm returns $`B_0`$ with those chosen diagonal
leaf blocks, which are free in the HSS class.
