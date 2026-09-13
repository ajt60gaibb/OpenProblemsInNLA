# Author-side mathematical audit

This note records checks performed while preparing the proof. It is not a
separate independent review, a peer-review report, or a formal certificate.
The theorem references below refer to the included manuscript.

## 1. Original model, input rank, and quantifiers

Theorem 1.1 fixes p = 4 but retains arbitrary input n, d, and rank. The output is
nonnegative weights on original indices. Every original-ambient projector
compresses on the row span to a positive contraction of rank at most k. Its
squared residual remains a_i^T(I-P)a_i, so the quartic cost is its square. The
upper proof preserves this larger positive-contraction query family, avoiding
an unproved invariance under a non-orthogonal change of coordinates.

The optimal head exists by compactness after row-span reduction. For a positive
contraction P, P is at most the projector onto its range, giving C(P) >= OPT.
After OPT is normalized to one, this supplies the lower cost scale needed for
relative estimates. A generic head would not supply this step. The random
finite tests do not pretend their generic heads are optimal.

When OPT is zero the input rank is at most k. The head-only proof is stated
separately, including zero-cost queries, and no division by OPT occurs. The
all-zero input returns an empty coreset.

## 2. Fixed features and singular cases

Lewis normalization is proved by determinant-one minimization. It is used to
bound head linear forms, followed by Gaussian averaging. It does not change
Euclidean projectors or allow projected rows in the output.

M is the quadratic-head covariance on its positive range, of dimension
D <= k(k+1)/2. N is the tail-squared-weighted linear-head covariance. All inverse
square roots act only on their positive ranges. If a row has a nonzero tail,
its head lies in the range of N; if its tail vanishes, its mixed feature is
zero. This proves the mixed contraction identity also for singular N. Both
rank-one N and zero N cases are included in the finite tests.

The mixed covariance satisfies sum(g_i g_i^T) <= I and sum ||g_i||^2 <= k.
It is not assumed to be exactly the identity. The regularized tail metric is
positive definite even when the unregularized tail tensor covariance is singular.

The probability vector is fixed once, before rounding. It averages four
normalized statistics, with the mixed statistic omitted when its rank is zero.
Every nonzero input row has positive probability. The five individual ratios
used in the variance table follow directly and have no dependence on min pi_i.

## 3. Exact expansion and query norms

The complete quartic expansion is written in equation (4.5). Its terms are:
pure head; head-quadratic/mixed; head-quadratic/tail scalar; head-quadratic/tail
quadratic; mixed square; scalar-tail/mixed; mixed/tail quadratic; pure tail
scalar; linear-tail matrix; and quadratic-tail tensor. No odd mixed term is
removed by an unproved cancellation.

The tests reconstruct every term and compare with actual Euclidean residual
costs for projectors and positive contractions. The proof gives the identities
for all queries, not just tested directions.

The query vectors satisfy ||a||^2 = H, ||z||^2 <= sqrt(H), ||p||^2 <= k,
and p^T R_t p <= 2. The original cost obeys H <= 16 C and C >= 1. Combining
these, rather than bounding every query norm separately by k, is what supplies
the relative error scale.

## 4. Positivity and the evolving measure

After a round, the new measure need not be pointwise dominated by the original.
The proof never assumes that it is. It maintains three upper matrix bounds on
the whole current measure, including frozen entries, and exactly preserves
three scalar statistics plus one D-dimensional vector statistic.

The common-mass active copies are a submeasure of that whole positive measure.
Their variance bounds are evaluated at the start of an outer round. During an
inner partial-coloring step, the still-fractional index set is a subset of that
fixed copy collection. Its unscaled feature variances are therefore dominated
by the same full-collection variances, even though the current coefficient
center is no longer zero. This distinction prevents a circular appeal to
matrix invariants at unproved inner states.

## 5. Coefficient constraints and matrix Gaussian series

A standard Gaussian on the increment subspace is a projected coefficient
Gaussian, not a family of independent coordinates in the original basis.
Lemma 2.4 proves that both left and right matrix variances decrease under that
projection. An orthonormal basis of the subspace restores an independent-series
representation for Tropp's theorem. The contraction statement also holds after
fixed right whitening or multiplication by a fixed output projection.

Thus every imposed exact constraint is compatible with the stated variance
table. The numerical tests check left and right contraction explicitly, rather
than sampling correlated coefficients and incorrectly treating them as independent.

## 6. Protected mixed directions and the codimension count

For each of the two sensitive mixed series, the top q right-variance directions
of the full active collection are preserved exactly. Each such direction costs
D scalar equations: the total is at most 2Dq, not 2q. With
q = floor(c0 m0/(32D)) and sufficiently large m0, there is room for these
constraints, D+3 scalar/vector constraints, and a small fixed fraction of the
active head directions.

The two mixed protected spaces remain fixed throughout an outer round. Active
subsets have smaller variances, so every later step remains controlled by these
same spaces. Their unprotected right operator norms are bounded by trace/(q+1).
If the protected count exceeds the feature dimension, the whole space is
protected; there is no missing-dimensional case.

The head protection may change between partial steps. Its remaining covariance
is bounded using trace(S)/(ell+1), and its quartic Gaussian width is of order
k^(3/2), with an absolute supremum. The proof adds a zero index when applying
Gaussian comparison; it does not confuse expected signed and absolute suprema.

## 7. The other mixed term: why anisotropic whitening matters

For X4 = g_i d_i^T/pi_i, a naive operator bound followed by ||p|| <= sqrt(k)
would introduce an unwanted rank factor. The proof instead uses

    R4 = B4 + (8/eta) I,
    ||Z4 R4^(-1/2)|| <= C sqrt(log dimension),
    p^T R4 p <= 12k/eta.

The whitening event is uniform over all query vectors. It follows from both
whitened variances being at most I, also after coefficient projection. The
query inequality uses the exactly maintained mixed trace and the individual
tail-mass ratio. No net over arbitrary-rank tail directions is inserted.

The pure quadratic tail term uses the *different* fixed metric R_t, for which
p^T R_t p <= 2. These two normalizations serve different purposes and are not
silently interchanged.

## 8. Partial coloring and fractional exceptions

The imported Rothvoss result is Lemma 9 of arXiv:1404.0339v4. Its arbitrary
starting point is needed and was checked in the page image, including the
codimension fraction (3/2) xi log_2(1/xi). It is not the zero-center-only theorem.
All norm constraints define symmetric convex sets in the increment subspace.
A fixed number of high-probability Gaussian events gives measure at least 1/2,
which exceeds the required exponential threshold when the active set is large.

At each partial step a fixed fraction of the remaining coordinates saturates.
The process stops with at most m0 fractional entries. The total increments
satisfy the exact constraints; no assertion is made that each Gaussian draw
itself has admissible positive coefficients.

At the outer step, actual masses are eta(1+x) with x in [-1,1], hence nonnegative.
Strictly fractional entries are frozen forever. The exact mass constraint
ensures at most half as many positive full copies for the next stage. This is
not an appeal to an unsupported full-sign coloring theorem.

## 9. Error accumulation and absence of hidden n or d factors

The full-copy masses double. Since every executed stage has n > m0 and total
mass at most one, eta < 1/m0. Consequently sum eta <= 2/m0 and
sum sqrt(eta) <= 4/sqrt(m0), for every executed prefix.

These bounds first close the three matrix-invariant inductions, then sum the
relative cost errors. With

    m0 = C0 L^4 (k^(5/2)/delta + k/delta^2),

the remaining D sqrt(k)/m0 term is absorbed by k^(5/2)/m0 because D <= k^2.
At most m0 entries freeze per outer round, and the number of rounds is O(L).
The support is therefore O(L^5 (k^(5/2)/delta + k/delta^2)).

Preliminary row reduction bounds n0 polynomially in k and 1/epsilon. The initial
common-copy count is also bounded polynomially, without depending on min pi_i.
The row-span dimension is at most n0. Therefore every final logarithm is bounded
by C log(2k/epsilon); neither log n nor log d from the original input survives.
The two positive reweightings compose on original indices, with accuracy
budgets epsilon/8 each.

## 10. Lower bounds and target coverage

The cubic-core spectral selection is only an input-column selection argument;
all query evaluations remain actual hyperplane normals. The auxiliary vectors
are orthonormal within each entire group, so there is no small-support cutoff.
Optimizing the variable core density yields
min(k^2/epsilon^2, k^(5/2)/epsilon, k^4). The arbitrary-rank block construction
separately yields k/(2304 epsilon^2). Their maximum is within a factor of two of
the R(k,epsilon) in Theorem 1.1. Small ranks are included by changing one absolute
lower constant; their bounded restricted branch never forces an epsilon-dependent
adjustment of that constant.

The dense hyperplane lower construction also permits signed reweightings. The
orthogonal-block lower bound uses nonnegativity. The main strong-coreset model
and both upper constructions use nonnegative weights throughout.

## 11. Limits of the checks

The finite suite verifies algebra, variance inequalities, singular cases,
projector geometry, and exact certificates. It does not validate the imported
asymptotic theorems, certify the positive-probability core lemma by exhaustive
sampling, implement the asymptotic partial-coloring oracle, or formally verify
the new proof. No independent audit was performed. No corresponding complete
unrestricted theorem for p != 4 is asserted.
