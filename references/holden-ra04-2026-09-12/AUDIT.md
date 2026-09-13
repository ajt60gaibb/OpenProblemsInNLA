# Mathematical audit and verification boundaries

## Status

This package does not resolve unrestricted RA-04. Its stated positive
results have written proofs and selected algebraic checks, but have not
been independently peer-reviewed or checked by a proof assistant.

## Assumptions retained throughout

The matrix is real; arithmetic in the theorems is exact; initialization is
an independent standard Gaussian block; `1 <= b <= k`; `t=ceil(k/b)`;
`m=bt <= rank(A)`; the leading `b`-step relative gap is positive; and
`epsilon,delta` are between zero and one half. The empty minimum for
`t=1` is one. The eigenvalues used in the argument are **squared** singular
values, not singular values. Padding from `k` to `m` is retained, and a
graph over the leading `m`-dimensional eigenspace gives the required
`k`-dimensional overlap by selecting the first `k` columns.

## Imported result

Only the transfer from a `(k,L)`-good starting block to all the requested
approximation guarantees is imported as an algorithmic theorem. The exact
source is Chen et al., arXiv:2508.06486v2, Imported Theorem 3.2, interpreted
with its Problem 1.1, which expressly states the right-singular-vector
energy convention. That paper attributes the good-start analysis to
Meyer, Musco, and Musco, Appendix F. This package does not rederive that
convergence theorem and does not infer a right-vector guarantee merely
from a left Ritz-vector error bound.

## Checks of the central arguments

**Graph reduction.** The actual object bounded is `F=K_T K_H^{-1}`. Its
value does not change under a common invertible coefficient-basis change.
The orthonormalization formula for `[I;F]` bounds the inverse leading
projection by `sqrt(1+||F||^2)`.

**Relative-window packing.** A window about one leading eigenvalue of
relative half-width `Delta/2` contains at most `b` leading eigenvalues,
counting multiplicities. All far-set indices are selected from eigenvalues
alone, not from the random Gaussian data.

**Generic invertibility.** A residue-class coordinate-vector assignment
turns the head Krylov matrix into scalar Vandermonde blocks. This proves
almost-sure invertibility, not a numerical conditioning bound.

**Recursive leave-one-out step.** Delete one row of the square head
matrix. The null vector defines a vector polynomial `P_i` based only on the
other Gaussian rows. Its value `z_i` at the deleted node cannot vanish:
otherwise division by `(x-lambda_i)` would produce a null interpolant in
a smaller, almost surely invertible far-set problem. Normalize `z_i` to
unit length. Then `h_i^T z_i` is conditionally standard normal. The
identity for `P_i` follows by unique interpolation on the far set. A
sorted subset preserves the required `b`-step relative gap.

**Fractional-moment argument.** The half moment of the inverse Gaussian
scalar is finite. Truncate on the Frobenius norm of the Gaussian head
before bounding the product of the smaller inverse and its Gaussian
starting block. Conditioning on the deleted row removes only a scalar
normal variable. No independence is assumed between a subproblem's
inverse and its own entries. Uniform induction gives the displayed
half-moment recurrence. A Gaussian exponential moment controls the
truncation event. Failure probabilities are not repeatedly substituted
into inductive quantiles.

**Uniform tail interval.** Translate each of `t` interior Chebyshev nodes
to zero; all shifted head nodes remain positive, and their relative gaps
do not decrease. A union bound followed by the discrete Chebyshev
coefficient formula gives a uniform interval bound with factor `2t-1`.
There is no continuum union bound.

**Two-step result.** All far submatrices have exactly `b` rows. The
square-Gaussian inverse bound therefore applies separately to each fixed
submatrix. A union bound is valid despite overlaps. The leave-one-out
normal scalars need not be mutually independent.

**Exact clusters.** The scalar Lagrange polynomials are exact block
indicators only under the stated equality of the leading eigenvalues
inside each block. The report does not replace a narrow interval by a
single level without justification.

**Raw-conditioning example.** Its dimension, clustered gap, and leading
spectral normalization are fixed while its smallest raw Krylov singular
value tends to zero in probability. This says nothing contradictory
about its Krylov subspace and is explicitly not a disproof of RA-04.

## Remaining proof obligation

The all-input fractional-moment bound contains `t log m` in addition to
the requested terms. Removing that factor uniformly is not established.
The sufficient interpolation condition `(IE)` would do so, but it is
not used as a theorem. There is no assertion that `(IE)` is necessary.

## What the scripts do not verify

The exact scripts do not validate Gaussian probability estimates,
universal quantifiers, or the imported convergence theorem. The numerical
scripts do not check all spectra or random seeds. They do not certify
exact rank in floating-point arithmetic or calculate a valid universal
constant. All such limitations are retained in the main report.
