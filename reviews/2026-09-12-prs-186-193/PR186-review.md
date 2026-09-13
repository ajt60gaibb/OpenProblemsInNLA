# PR 186 independent matrix partial-results audit

**PASS for the stated partial results and supporting reductions.** Reviewed
`fc83d2959723c92967a26777e5238404804c848c` against published base
`5830ed4fb06da0659414a3deb2a40ad327aca052`, on 12 September 2026.
Reviewer: coordinating Codex AI agent. This is mathematical/source auditing,
not external human peer review, a priority finding, or Lean verification.

I read all four actual proof documents, the complete exact MI-15 checker,
MI-16 checker, MI-20 reduction checks, MI-27 family checker, corruption controls,
and the four canonical statements. Submitted PASS reports were not used as
proof evidence. A separate reviewer cross-checked MI-16/20/27 and publication.

## MI-15: five finite-order SOS certificates

The target is the actual quartic in all independent real Toeplitz variables;
no symmetry, band restriction or positivity is imposed. The wedge identity
has the correct factor two and Toeplitz multiplicity weights. Central-index
wedges contribute 2n-2 explicit quadratic squares and cancel from every
commutator entry. The Plucker corrections vanish identically on actual wedges.

The complete supplied verifier separately expands every coefficient of the
canonical quartic and checks equality with the represented polynomial. It
checks the n-1 disjoint kernel indicators and a spanning rational complement.
Exact strict diagonal dominance of T-transpose G T proves positive definiteness;
it also proves T is invertible, so invertibility of a rounded numerical factor
is not assumed. The remaining Gram matrix has rank 2(n-1)(n-2). The spectral
theorem then supplies real quadratic squares; adding the central squares gives
at most 2(n-1)^2. Rational coefficients of the individual squares are neither
needed nor incorrectly claimed.

All five full coefficient/kernel/positivity checks for orders 8–12 passed in
a fresh rerun. Both deliberate corruptions were rejected. I additionally wrote
an independent implementation using actual Toeplitz basis matrices and their
matrix commutators, without importing submitted code. Exact object-integer
matrix products reconstruct all five Gram matrices, kernel complements and
positive congruences. Their ranks are 84,112,144,180,220; all five minimum
integer margins match the publication. Another 125 signed-integer evaluations
compare the actual matrix quartic to the complete Gram expression.

These are five complete finite-order certificates, not an all-order induction.
The Partially resolved status and explicit remaining gap are correct.

## MI-16: one exceptional eigenvalue

Every complex Hermitian matrix with spectrum (alpha,beta,...,beta) is
beta I + (alpha-beta)uu*, including coincident and zero eigenvalues. In the
permanent expansion, each selected j-row rank-one term contributes j! times
the product of its squared coordinate moduli; complex phases cancel. Thus the
whole orbit reduces to the stated symmetric multiaffine polynomial on a simplex.

The minimum-support maximizer lemma is valid even when coefficients have mixed
signs: fixing two positive coordinates and their sum gives C+As+Bxy. Negative
B contradicts maximality, zero B contradicts minimal support, and positive B
forces equality of the coordinates. Therefore a maximum occurs on an equal
positive support, and comparing the n support-size polynomials is an exact
finite answer for this spectral class. It is not a restatement of the original
unitary optimization. For alpha >= beta, monotonicity of each normalized
elementary symmetric term proves full-support optimality. The beta=0,
alpha=beta, n=1 and all-zero cases obey the same formula. The alpha<beta case
correctly permits smaller supports, illustrated by (0,1,1).

Fresh supplied exact checks passed: 72 rational permanent expansions,
126 support representatives, and 1,650 rational simplex points. These support
the analytic proof; they do not prove an arbitrary-spectrum formula. Changing
Open to Partially resolved is appropriate.

## MI-20: dimension-preserving binary and general dilated reductions

The positive dual formulation follows from polar decompositions extended to
unitaries and genuine Schatten duality, with both directions and nonzero
denominators valid. I checked its attribution against
[Qiu, Proposition 3.1](https://arxiv.org/html/2608.17565v2), which treats all
summand counts and 1<p<infinity. The known ingredient is credited explicitly.

For fixed binary S,R, every feasible split is S^(1/2) K S^(1/2) on the support
of S. Convexity and a spectral convex decomposition of 0<=K<=I yield a
projection optimizer of any rank, with no false rank-one conclusion. For
general m, extending the normalized positive pieces on ker S gives a POVM;
the stacked square-root map W is an isometry. Coordinate projections in
dimension mn reproduce every original piece as W X_j W*, and likewise
preserve R,S and every relevant singular value up to appended zeros. Both
directions of equality of dimension-free suprema follow. The manuscript
correctly distinguishes this from a fixed-dimension reduction for m>2.

Padding and tensor-product lower bounds are valid using approximating sequences.
Fresh numerical checks reproduced eight archived ratios and twelve dilation
cases, including singular S. These are sanity checks, not global optimization.
No sharp function is determined, and Open is correct.

## MI-27: variable-trace projection equivalence and coefficient sharpness

The positive regularization epsilon I+(1-2epsilon)P keeps both original
matrices strictly positive and passes to the projection case with S fixed.
Conversely the spectral layer decomposition is a convex combination of
projections, including zero. Linearity, norm convexity and binary-entropy
concavity give the bound at the recombined trace. Varying the component traces
is essential and explicitly retained; no fixed-trace extreme-point assertion
is used. Endpoint ranks are covered by entropy continuity.

The 2-by-2 family has middle-factor eigenvalues t^2 and 1-t^2, so both A and B
are strictly positive for 0<t<1/2. The two commutator singular values are the
displayed off-diagonal magnitude. With b_t/(2t) tending to one, elementary
logarithmic asymptotics make the ratio tend to one. This proves that every
coefficient below one fails on valid original-domain examples; it does not
establish the coefficient-one upper bound. Fresh exact positivity and trace
checks passed at eight rational t values; the high-precision ratios are
explicitly supplementary numerical evidence. Open is correct.

## Evidence and limits

Independent MI-15 code and output are `/private/tmp/nla-pr186-independent-mi15.py`
and its matching JSON; supplied rerun logs are `/private/tmp/nla-pr186-MI-15-tests.log`
through MI-27, with separate MI-15 corruption-control JSON. The original
pre-publication attachment is not independently authenticated by this review;
the complete submitted final mathematical content is what was audited.
IDs, original targets, historical ratings and prior-source credit are retained.
No change to a full-solution status is warranted for these four contributions.
