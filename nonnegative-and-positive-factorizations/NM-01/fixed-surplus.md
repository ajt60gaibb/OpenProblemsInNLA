# Exact minimum-volume decision with a bounded column surplus

The [NM-01 promise](README.md#problem-statement) admits an exact deterministic
polynomial-time algorithm whenever the difference between the number of hull
vertices and the rank is bounded by a fixed constant. The rank may grow with
the input. In particular this applies when $`n-r`$ is bounded. The argument
combines the maximum-volume inscribed ellipsoid approach of
[Lin, Wu, Ma, Chi, and Wang](https://arxiv.org/abs/1708.02883v3) with facet
enumeration in this parameter regime and an exact binary threshold comparison.

## Rational affine coordinates and the optimal value

Choose $`r`$ linearly independent columns $`x_1,\ldots,x_r`$ of $`X`$, put
$`d=r-1`$, and set $`D=[x_1-x_r,\ldots,x_d-x_r]`$. Write the affine coordinates
of every data column as $`x_r+Dy_i`$. They exist on promised inputs because all
columns of $`X`$ are in the affine hull of the columns of $`W_\star`$, of
dimension $`d`$. Their rational coordinates, computed by linear equations, have
polynomial bit length. Put $`P=\operatorname{conv}\{y_i\}`$ and
$`\kappa=\det([D,x_r]^T[D,x_r])>0`$. For a containing simplex with vertices
$`s_1,\ldots,s_r`$ in these coordinates, set
$`T=[(s_1,1)^T,\ldots,(s_r,1)^T]`$, with the last row equal to one. Its factor
$`W=[D,x_r]T`$ obeys $`\det(W^TW)=\kappa(\det T)^2`$. Conversely any feasible
factorization defines a containing simplex in these coordinates. Both
factors have rank $`r`$, and the column normalization implies the data lie
in the affine hull of the $`r`$ columns of $`W`$. Both affine hulls have
dimension $`r-1`$, so they coincide.

The section of $`\mathcal C_r`$ on $`e_r^Th=1`$ is the inscribed ball of the
standard simplex in $`\mathbb R^r`$. Indeed on that hyperplane
$`\|h\|_2^2=1/r+\|h-e_r/r\|_2^2`$, so the radius is
$`1/\sqrt{r(r-1)}`$, the distance from $`e_r/r`$ to each coordinate facet.
By column normalization the same section of the cone of $`H_\star`$ is the
convex hull of its columns. Thus the data hull contains the affine image of
this ball under the map from the standard simplex to the hidden simplex
$`S_\star`$, and is contained in $`S_\star`$. The ball is the maximum-volume
inscribed ellipsoid of the standard simplex. Existence and uniqueness of
that ellipsoid, and invariance under permutations of the coordinates, force
its center to be $`e_r/r`$ and its shape on $`e_r^Tz=0`$ to be a scalar
multiple of the identity. It follows by inclusion and affine invariance that
the image of the ball is a maximum-volume inscribed ellipsoid of $`P`$.

Write this ellipsoid in $`y`$ coordinates as $`c_\star+M_\star B_d`$, where
$`B_d`$ is the unit Euclidean ball and $`M_\star`$ is symmetric positive
definite. In $`\operatorname{conv}(0,e_1,\ldots,e_d)`$ the ellipsoid has shape
matrix $`M^2=(rd)^{-1}(I_d-e_de_d^T/r)`$, obtained by retaining the first $`d`$
coordinates of the standard simplex in $`\mathbb R^r`$. The determinant is
$`1/(d^d r^{d+1})`$. An affine map from this reference simplex to one with
augmented vertex matrix $`T`$ multiplies volume by $`|\det T|`$. Therefore every
containing simplex has $`|\det T|`$ at least that of $`S_\star`$, and the minimum
in (MV) is

```math
v_\star=K\det(M_\star)^2,\qquad K=\kappa d^d r^{d+1}.
```

## Facet enumeration and a rational gap

At the tangency point of any facet of $`S_\star`$ with its inscribed ellipsoid,
every supporting hyperplane of $`P`$ also supports the ellipsoid. The
ellipsoid has a unique supporting hyperplane there. A full-dimensional
polytope point with a unique supporting hyperplane is in the relative
interior of a facet. Thus every facet of $`S_\star`$ is supported by a facet of
$`P`$. Each such hyperplane has a rational equation of polynomial bit length,
since it is specified by $`d`$ affinely independent rational input vertices.
Solving $`d`$ of these equations gives each vertex of $`S_\star`$. Clearing
denominators and using determinant bounds in these two linear systems and
in the determinant formula proves that $`v_\star`$ has a denominator at most
$`2^b`$, for a computable $`b`$ polynomial in the binary input length. The
same argument gives rational feasible factors of polynomial bit length, so
yes-instances have polynomial-size rational certificates on the promise.

Remove duplicate columns and test each remaining point for membership in
the convex hull of the other points by rational linear programming to obtain
the $`v`$ distinct vertices. Enumerate the $`\binom{v}{d}`$ subsets of size
$`d`$ and keep the affine hyperplanes spanned by each affinely independent
subset with all of $`P`$ on one side. This gives all the facet inequalities
in $`\binom{v}{d}`$ times polynomial bit time. When $`v-r`$ is bounded, the
number of subsets is polynomial in $`v`$ because $`v-d=v-r+1`$ is bounded.

## Computing the decision in binary bit complexity

Given the facet inequalities $`a_i^Ty\le b_i`$, maximize $`t`$ over

```math
M\succeq0,\qquad 0\le t\le(\det M)^{1/d},\qquad
\|Ma_i\|_2\le b_i-a_i^Tc\quad\text{for each }i.
```

This is a convex body in the real variables $`(c,M,t)`$ and its optimum is
$`t_\star=(\det M_\star)^{1/d}`$. The eigenvalues of $`M`$, the norm of $`c`$,
and $`t`$ are bounded by any rational $`U\ge1`$ bounding the norms of the data
points. For $`M`$ this follows by considering both $`c+Mu`$ and $`c-Mu`$ for
unit $`u`$. The combined outer radius can be taken to be $`(d+2)U`$. For a
known interior ball, the reference simplex is contained in $`P`$ by the
choice of coordinate basis and contains $`B(e_d/r,4\rho)`$ for
$`\rho=1/(4r^2)`$. A ball of radius $`\rho/8`$ about
$`(e_d/r,\rho I_d,\rho/2)`$ in the combined Euclidean and Frobenius norms is
inside the feasible body. Each perturbed ellipsoid stays within
$`B(e_d/r,4\rho)`$ and has all eigenvalues of $`M`$ greater than $`t`$. These
norm bounds yield rational inner and outer radius bounds also in the
ordinary coordinates of the independent matrix entries, by reducing the
inner radius by another factor of two.

The body admits rational separation in polynomial bit time. Each norm
constraint is the positive semidefiniteness of the block matrix with
diagonal blocks $`(b_i-a_i^Tc)I_d`$ and $`b_i-a_i^Tc`$, and off-diagonal
block $`Ma_i`$. Rational symmetric elimination tests these matrices and
$`M`$, returning a rational negative quadratic form for a violation. For the
determinant constraint, suppose $`M\succeq0`$, $`t>0`$, and $`\det M<t^d`$.
If $`M`$ is singular, first replace it by $`Q=M+\delta I_d`$ with rational
$`\delta>0`$ small enough that $`\det Q<t^d`$. This takes polynomial bit
precision using $`\det Q\le\delta(1+\|M\|_2)^{d-1}`$ when $`\delta\le1`$.
Otherwise take $`Q=M`$. Choose a rational $`\alpha`$ strictly between
$`(\det Q)^{1/d}`$ and $`t`$ by bisection with rational powers. Polynomial
precision suffices because $`t^d-\det Q`$ is a positive rational of polynomial
bit length and $`x\mapsto x^d`$ has a derivative with polynomial bit-size
upper bound on $`[0,t]`$. For every positive semidefinite $`N`$, the
arithmetic–geometric mean inequality for eigenvalues gives

```math
(\det N)^{1/d}\le (\det Q)^{1/d}\,
\frac{\operatorname{tr}(Q^{-1}N)}{d}.
```

Thus every feasible $`(c',N,t')`$ satisfies
$`t'\le\alpha\operatorname{tr}(Q^{-1}N)/d`$, which separates the query since
$`\operatorname{tr}(Q^{-1}M)\le d`$. This also establishes concavity of the
determinant root on positive definite matrices by taking the infimum of
its affine majorants and extending by continuity.

[Weak optimization from separation](https://www.zib.de/userpage/groetschel/pubnew/paper/groetschellovaszschrijver1981a.pdf)
now approximates $`t_\star`$ to additive error $`\epsilon`$ in time polynomial
in the facet description length and $`\log(1/\epsilon)`$. Clamp the
approximation to $`[0,U]`$ and evaluate $`K t^{2d}`$ exactly at that rational
point. If $`q`$ is the denominator of the input threshold, then
$`\gamma=1/(q2^b)`$ bounds every nonzero difference $`|v_\star-\tau|`$ from
below. Choose $`\epsilon`$ so that $`2d K U^{2d-1}\epsilon\le\gamma/4`$.
Its logarithmic precision is polynomial in the input length. The exact
decision is yes if and only if the computed value is at most
$`\tau+\gamma/2`$, including when $`v_\star=\tau`$.

On inputs outside the promise, the algorithm can reject rank, affine
dimension, or vertex-count failures. Its runtime stays polynomial for a
fixed surplus bound, and its answer is required to be correct only on
inputs with that bound and the NM-01 promise. The unrestricted case still
requires a method that avoids the potential exponential facet enumeration
or a hardness argument preserving the promise.
