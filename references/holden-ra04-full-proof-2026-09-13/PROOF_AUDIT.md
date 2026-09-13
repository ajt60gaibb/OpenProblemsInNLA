# Mathematical self-audit

This records the checks made during development of the proof. It is not an independent referee report or a formal verification certificate. No unresolved mathematical premise is knowingly used by the manuscript, but independent scrutiny is still needed before treating a new full-resolution claim as established.

## Dependency chain

The manuscript's main theorem depends on the following chain, with theorem numbers referring to `report.pdf`.

| Result | Inputs | Role |
|---|---|---|
| Lemma 2.1 | Relative `b`-step separation; residue-class Vandermonde witness | Shows that the determinant is a nonzero degree-`m` homogeneous polynomial in the starting matrix. |
| Lemma 2.2 | Pascal translation and uniqueness of interpolation | Proves that a common node shift preserves both the determinant and the singular locus exactly. |
| Lemma 3.1 and Corollary 3.2 | Elementary interval selection and factorization of a scalar polynomial | Give an exponential-in-degree lower bound on complete circles outside logarithmic intervals of degree-independent total length. |
| Lemma 4.1 | Root covering, moment equations, and well-conditioned contiguous row blocks | Gives a quantitative lower bound for the product of the minimizing residual and an anchored scalar polynomial. |
| Lemma 5.1 | Attained variational minimum and Lemma 4.1 | Produces a unit Frobenius direction in which the reciprocal extrapolation norm has negative upper directional derivative. |
| Lemma 5.2 | Continuity, compact-ball minimization, and Lemma 5.1 | Converts bad extrapolation into proximity to the determinant-zero locus. |
| Lemma 6.1 | Published real-algebraic tube theorem | Bounds the probability of proximity to that locus, with polynomial dependence on degree and ambient dimension. |
| Lemma 6.2 | Elementary Gaussian estimates | Controls contiguous row-block singular values and the norm of the starting matrix. |
| Theorem 6.3 | Lemmas 5.2, 6.1, and 6.2 | Establishes the anchored extrapolation bound at zero. |
| Theorem 6.4 | Theorem 6.3's explicit event and Lemma 2.2 | Controls every tail evaluation on the same event. |
| Theorem 1.1 / Section 7 | Graph construction, Theorem 6.4, and the established good-start convergence theorem | Proves the requested algorithmic rate and all three output guarantees. |

Neither the old fractional-moment recurrence nor its unproved sharp interpolation strengthening is an assumption in this chain.

## Root covering and annular identity

For `s` logarithmic root locations, a bad point has its `j`th nearest location at distance less than `jh/s`. The corresponding intervals have only `s` possible radii. Greedy selection by decreasing radius gives disjoint selected intervals; the sum of their enclosed root counts is at most `s`. Their lengths sum to at most `2h`, and closed triple dilates cover the bad set in their interior with total length at most `6h`.

The product estimate uses `s!/s^s >= exp(-s)`, rather than replacing every root separation by `h/s`. This is the step that avoids an unnecessary `t log t` loss. Repeated roots are counted with multiplicity. Since the scalar polynomial has value one at zero, none of its roots is zero. The reverse triangle inequality depends only on root moduli, so complex roots are handled on entire circles, not just along the positive real axis.

The annular construction additionally pads **every** logarithmic head node by `gamma=Delta/(64m)`. Together with the root cover, the union has length at most `Delta/8`. Every component containing nodes therefore contains at most `b` nodes, with multiplicities included. The component's node indices are contiguous. A smaller contiguous row set inherits the lower singular-value bound from a contiguous `b`-row block by zero padding.

At each boundary radius, the distance in logarithmic coordinates from every node is at least `gamma`. The contour estimates are thus valid against all head nodes, not only those in the selected component. For

```math
w=\operatorname{diag}(\phi(\lambda_i))u,
\qquad H^T\Lambda^j u=0\quad(1\le j\le t-1),
```

the polynomial `x(phi(x)-phi(z))/(x-z)` has degree at most `t-1` and zero constant coefficient. This gives the exact resolvent identity used in Lemma 4.1.

The contour integral has outer counterclockwise and inner clockwise boundaries. On the left-hand side, each coordinate uses

```math
\frac{\lambda_i}{z(z-\lambda_i)}=
\frac1{z-\lambda_i}-\frac1z.
```

The pole at zero cancels between the two circles, leaving exactly the node residues of the component. The right-hand expression contains `1/phi(z)`, but no claim that `phi` is root-free inside the annulus is needed. The identity is used on the boundary, and residues are calculated for the equal left-hand expression, which has no such denominator. Repeated eigenvalues contribute sums of residues from their indexed rows.

The factor `1/z` cancels the circle length in the norm estimate. This is why no leading spectral ratio enters. Summing squares over at most `m` node-containing components gives the claimed lower bound

```math
\|\operatorname{diag}(\phi(\lambda_i))u\|_2
\ge\frac{\mu\gamma\rho}{4\sqrt m R},
\qquad\rho=(\Delta/(128e))^{t-1}.
```

## Variational minimum, nonsmoothness, and distance

Invertibility of the head matrix identifies all coefficient vectors with interpolation data. Therefore the minimum of the residual norm under `||P(0)||=1` is exactly `1/||E(0)||`, and a right singular vector of `E(0)` gives an attained minimum. No compactness is assumed for the unbounded set of polynomial coefficients.

Only positive-degree coefficients are varied when deriving the moment equations. This leaves the normalization of the constant coefficient unchanged. The scalar polynomial is `phi(x)=P(0)^T P(x)`, so it is anchored at one and is pointwise bounded by `||P(x)||`.

The descent direction is built from one chosen minimizing polynomial and then that polynomial is held fixed as the matrix moves. This proves an **upper directional derivative** inequality for the minimum. It does not require differentiability of the minimum, a simple extremal singular value, or a unique minimizer. The tied-singular-value regression fixture explicitly checks this aspect in a finite example.

The local distance lemma does not integrate a potentially discontinuous gradient field. It argues by contradiction on a compact ball disjoint from the singular locus: the continuous function

```math
f(X)+(\alpha/2)\|X-H_0\|_F
```

has boundary values strictly above its value at the center and hence an interior minimizer. The descent inequality decreases the first term faster than the Lipschitz penalty can increase, contradicting minimality. Its conclusion is a lower bound for `f` in terms of distance to singularity in **starting-matrix coordinates**. It is not a statement about unstructured distance from the raw Krylov matrix to all singular matrices.

## Real-algebraic probability theorem

The imported source is the real theorem in Bürgisser–Cucker–Lotz, arXiv:math/0610270v1, Theorem 1.1, PDF page 4. Its algebraic set may be singular. The distinct complex conic result is not substituted.

For `t>=2`, the ambient real dimension is `N=mb>=2`, so the sphere parameter is `p=N-1>=1`. The zero set of the head determinant is proper by the explicit Vandermonde witness and contains nonzero zero-row matrices. The determinant is homogeneous of degree `m`. These facts verify the source's geometric hypotheses. A standard Gaussian direction is uniform on the sphere, and the condition number is unchanged by radial scaling.

The manuscript derives the concrete tail bound `40 d0 p/v` from the source's displayed finite sum for `v>=3 d0 p`. In the application, `d0=m` and `v=160mp/eta`, which satisfies that threshold. Degree and ambient dimension are polynomial parameters; spectral coefficient magnitudes do not appear in the source theorem.

Four events are combined by a union bound, each with failure probability at most `eta/4`. They need not be independent. Row-block lower bounds apply to at most `m` fixed contiguous blocks. The norm lower bound is obtained from one scalar entry, not from an unjustified inverse-norm expectation.

## Constants and simultaneous evaluation

On the four-event intersection, the choices are

```math
R_0=2\sqrt{mb/\eta},\quad
\tau=\eta/(4mb^{3/2}),\quad
r_0=\tau/2,\quad
\mu=\tau/2,\quad R=2R_0.
```

Weyl's singular-value perturbation bound and the Frobenius norm ensure that these local row and norm bounds hold throughout the required ball. The inequalities used are

```math
\operatorname{dist}_F(H,\Sigma_\lambda)\ge\eta^2/(640m^3),
\quad r_0\ge\eta^2/(640m^3),
\quad \alpha\ge\eta^{3/2}\Delta\rho/(8192m^5).
```

Thus

```math
f(H)\ge\eta^{7/2}\Delta\rho/(10485760m^8)
\ge 2^{-24}m^{-8}\eta^4(\Delta/(128e))^t.
```

The last inequality deliberately weakens the constants. The endpoint `t=1` is handled directly by a Gaussian inverse bound, including `m=b=1`, without invoking a sphere theorem with dimension zero.

For every `0<=x<lambda_m`, shifting all nodes by `x` preserves positivity, does not decrease the relative gap, and leaves the determinant polynomial **identical**. All four events and the local ball consequently remain exactly the same. This gives a deterministic implication for every shift on one event, not an uncountable union of probabilistic assertions. Polynomial continuity gives `x=lambda_m`.

## Algorithmic transfer and edge cases

The graph identity has tail rows `T_j^T E(lambda_tail,j)`. Its squared norm is bounded by the tail Frobenius norm squared times the uniform interpolation norm squared. With `eta=delta/2`, the explicit graph bound is

```math
L\le1+2^{57}n^{18}\delta^{-9}(128e/\Delta)^{2t}.
```

The first `k` graph columns give the good-start overlap bound even when `b` does not divide `k`. The simulated starting matrix uses only the original Gaussian block and its original Krylov powers. The nesting identity is exact.

The convergence dependency is Imported Theorem 3.2 of Chen et al., arXiv:2508.06486v2, checked together with the **right-vector** convention of Problem 1.1. The proof is not inferred from a left-vector-only guarantee. Its absolute constant is denoted `C0>=1`. Elementary logarithmic inequalities give `log(nL/epsilon) <= 80[t log(2/Delta)+log(n/(delta epsilon))]`; the original count with `C=80C0+4` absorbs integer offsets and starting depth.

If `lambda_{k+1}=0`, the assumptions force `rank(A)=m=k`. Multiplying the first `t`-block head Krylov matrix by the positive diagonal head eigenvalue matrix shows that the powers from one through `t` span the complete range of `A`. Thus depth `t+1` gives exact recovery, without a limiting positive-tail argument.

## Scope of the checks

The self-audit found no remaining unproved step in the claimed argument. Finite symbolic and numerical checks support identities and implementations but cannot verify every spectrum, dimension, failure probability, or contour construction. The highest-priority independent review targets remain the annular nondegeneracy lemma, the variational descent-to-distance argument, and the exact common-event translation step. Acceptance as an independently verified solution is not claimed by this package.
