# NR-02 counterexample proof

Minhao Liu's construction disproves additivity for the full slack matrices
in [NR-02](README.md). The argument below uses a limit of column-scaled
submatrices to prove the nonnegative-rank gap and checks the facet condition
directly. Liu's quantitative proof gives the explicit 24-dimensional example
with extension complexities 40 and 79. [Liu, Theorem 1 and §§2–5](https://arxiv.org/html/2611.33631v1).

## The gap in nonnegative rank

Use Liu's graph with six clusters $`C_0,\ldots,C_5`$ of two vertices each.
Join each vertex of $`C_j`$ to both vertices of $`C_{j+1}`$. Indices of clusters
are taken modulo six, and edges joining these clusters have type $`j`$.
In the 24 edge coordinates, let $`R_v`$ be the indicator of the four edges
at vertex $`v`$. Let $`A_s`$ indicate edge type $`2s`$ and $`X_t`$
indicate types $`2t+2,2t+3,2t+4`$, for $`s,t\in\mathbb Z/3\mathbb Z`$.
For an integer $`L>0`$, the matrix $`M_L`$ has all 39 columns
$`X_t`$ and $`X_t+LR_v`$. Write $`M_L^{[d]}`$ for the matrix of all
vertical stacks of $`d`$ of its columns, including repetitions.

The identities

```math
X_t=A_{t+1}+\sum_{v\in C_{2t+4}}R_v
   =A_{t+2}+\sum_{v\in C_{2t+3}}R_v
```

hold by checking the three edge types. Thus a column with index $`t`$
can use either label in $`\{t+1,t+2\}`$ along with the twelve star vectors
$`R_v`$. Two labels suffice to meet all three possible label sets for
a single column. For a stacked pair, use a label common to its two
sets, with coefficient one on $`(A_s,A_s)`$. This gives upper bounds
14 and 27 for the nonnegative ranks of $`M_L^{[1]}`$ and $`M_L^{[2]}`$,
using twelve star generators in each block and three shared
label vectors for the pair.

For the lower bounds, fix $`d\in\{1,2\}`$. In $`M_L^{[d]}`$, keep the
columns $`(X_{t_1},\ldots,X_{t_d})`$, as well as the stacks with
$`X_0+LR_v`$ in one block and $`X_0`$ in every other block. Divide the
latter columns by $`L`$. As $`L\to\infty`$, the resulting submatrix
converges to a matrix with two kinds of columns, the stacks of $`X_t`$
and a single star in a single block with zeros elsewhere.

In a fixed format the matrices of nonnegative rank at most $`r`$ form a
closed set. In any convergent sequence, normalize the nonnegative generators
to have maximum entry one. Pad each list to length $`r`$ using unused
generators. At a coordinate where a generator attains one, its coefficient
is bounded by the largest entry of the column being represented. Both
the generators and all coefficients thus admit simultaneous convergent
subsequences, giving a factorization of the limit. Column selection and
positive column scaling cannot increase nonnegative rank.

Suppose the limit matrix had at most $`13d`$ generators. Fix a
representation of every column. A generator used in a star column must
have its support in that star. A generator used by two distinct stars
is supported on their common edge, so it can serve at most two stars
and both are in the same block. Call a generator private to a star if
that is the only star representation that uses it.

If $`b`$ vertices lack a private generator, all the edges incident to
those vertices must each have a generator shared by two stars. Distinct
edges require distinct shared generators. For $`b=1`$ this costs four
generators, for $`b=2`$ at least seven, and for $`b\ge3`$ at least
$`2b`$, since there are $`4b`$ incidences. Adding the private generators
for the other $`12d-b`$ vertices exceeds $`13d`$ in every case. Hence
we can reserve one private generator for each vertex. At most $`d`$
generators remain.

Choose a block whose stars use at most one of the remaining generators.
Such a block exists because each remaining generator can serve stars in
at most one block. Choose a cycle on one vertex from each cluster of
this block, avoiding the vertices whose stars use that remaining generator.
At most the two endpoints of an edge must be avoided, in different
clusters. On the cycle take the alternating sum of edge coordinates,
with positive signs on even edge types. It vanishes on every star and
has value one on each $`X_t`$.

The reserved generator of any vertex whose star uses no remaining
generator is a multiple of its entire star. All other reserved
generators in the chosen block are supported on stars at the avoided
vertices and vanish along the cycle. The remaining generator used by
stars also vanishes along this cycle, as do the generators used by
stars in other blocks. Every stack of $`X_t`$ therefore needs a positive
contribution from a generator that has no use in a star column.

Each such generator is forbidden in some stack because it has a
positive coordinate where at least one $`X_t`$ vanishes. Thus one
remaining generator is insufficient for $`d=1`$. For $`d=2`$ there
must be two remaining generators and neither is used by a star. The
reserved generators are then all multiples of full stars, so the
alternating sum must get a positive contribution in **both** blocks.
Take a stack forbidding the first remaining generator. The second
must contribute in both blocks and hence have nonzero entries in both.
Exchanging the generators shows the same for the first. In each block
a positive entry excludes at least one of the three choices of
$`X_t`$, so either generator can serve at most four of the nine stacks.
The two generators cannot cover them all. This proves the lower
bounds and, by closedness, gives the ranks 14 and 27 for all sufficiently
large integers $`L`$.

## From selected rows to full slack matrices

Let $`B_L`$ be the convex hull of the columns of $`M_L`$. The twelve
$`R_v`$ have exactly one linear relation up to scaling, with coefficients
$`+1`$ on even clusters and $`-1`$ on odd clusters. In fact a linear
relation assigns vertex weights whose sum across every edge is zero.
Connectedness and bipartiteness give the stated relation. Moreover,
$`X_1-X_0`$ is the difference of the sums of stars of clusters 0 and 3,
and $`X_2-X_0`$ is the difference for clusters 1 and 4. Thus $`B_L`$
has affine dimension 11.

For an edge $`e`$, take $`t`$ with $`X_t(e)=0`$. The face
$`x_e=0`$ contains $`X_t`$ and the ten points $`X_t+LR_v`$ for
vertices outside the two endpoints of $`e`$. The ten difference
vectors are linearly independent, because the only relation on all
twelve stars uses every star. The face has dimension ten, since
an incident star also gives a point with positive $`e`$-coordinate.
For a different edge $`f`$, an endpoint of $`f`$ outside $`e`$ gives
a point of the face with positive $`f`$-coordinate. Consequently all
24 coordinate inequalities are distinct facets.

Take just these facet rows of the full slack matrix of $`B_L`$.
The resulting matrix has the same nonnegative rank as $`M_L`$.
Every true vertex is a generating point, and each remaining column
is a convex combination of true vertex columns. For $`B_L\times B_L`$
the selected rows have the same rank as $`M_L^{[2]}`$ by taking
products of the convex combination coefficients.

For each omitted facet with slack $`\sigma(x)`$, introduce
one coordinate $`z`$ with $`0\le z\le\sigma(x)`$. The resulting
polytope has precisely the retained facets and the two endpoint
facets per added coordinate. For a retained facet, choose a point
in its relative interior and choose the new coordinates strictly
inside their intervals. For an endpoint facet, take an interior
base point and put just that coordinate at an endpoint. These
choices give the required codimension-one faces. The vertices of
the new polytope lie over vertices of the base and choose an
endpoint in every interval. Indeed, an interior interval coordinate
can vary in both directions. Fixing an endpoint choice for every
interval gives a face affinely isomorphic to the base.

Consider adding one pair of endpoint rows to the selected row
matrix $`M`$, allowing duplicate columns. For each column $`M_i`$,
the new columns are $`(M_i,\sigma_i,0)`$ and
$`(M_i,0,\sigma_i)`$, with $`\sigma_i\ge0`$. The rank goes
up by at most two using one unit vector for each new row. In a
factorization with at most $`\mathop{\mathrm{rank}}\nolimits_+(M)+1`$
generators, discard generators that are unused. A generator positive
in both new rows could serve none of the columns. Each new row must
have exactly one generator with a positive entry there. At least one
is necessary because $`\sigma`$ is nonzero. Two for either row would leave fewer than
$`\mathop{\mathrm{rank}}\nolimits_+(M)`$ generators for the columns
with that row zero. Each of the two generators must vanish on
every old row. For a retained facet row, choose a vertex on that
facet away from the omitted facet, so its old slack is zero and
$`\sigma_i>0`$. For an earlier endpoint row, choose its zero
endpoint over any vertex with $`\sigma_i>0`$. Each choice forces
the uniquely used new-row generator to be zero in the old row.
The remaining generators could then generate all columns of $`M`$ with fewer than
$`\mathop{\mathrm{rank}}\nolimits_+(M)`$ generators, a contradiction.
The same reasoning applies successively to all omitted facets.

If $`k`$ facets of $`B_L`$ were omitted, wedge over all of them to
obtain a polytope $`P_L`$. It is rational and full-dimensional in
affine coordinates. Its full slack matrix has nonnegative rank
$`14+2k`$. Wedging over the corresponding $`2k`$ facets of
$`B_L\times B_L`$ gives precisely $`P_L\times P_L`$.
Its full slack matrix has nonnegative rank $`27+4k`$. The
facets and vertices of a Cartesian product give the stacked
matrix in NR-02, and $`27+4k<2(14+2k)`$ proves the strict
inequality.

## Exact checks of Liu's specified instance

At $`L=10^6`$, the catalog audit reconstructed all 39 columns and checked
the shared-generator representation for each of the 1,521 stacked pairs.
It checked 37 irredundancy witnesses, the active constraint ranks of all
39 base vertices, and the count of 150 endpoint lifts in Liu's
description of $`P`$. It also checked the two strict rational bounds
used in Proposition 9. These calculations used integer arithmetic
and rational Gaussian elimination.
