# AV-03 self-review

## Classification and strongest limitations

The original arbitrary-matrix problem is NOT solved. The complete proof
candidates here concern two explicitly restricted matrix structures, explicit
algorithmic obstructions, and an exact handicap formula for a 3 by 3 family.
Do not promote any of these to a complete positive or negative resolution of
AV-03. In particular, a large handicap is not an algorithmic lower bound.

## Checks performed

- The canonical quantifiers, rational binary input, deterministic bit model,
  exact output, n>=1, and absence of a supplied regularity certificate are
  recorded in `result.md`. The solvers do not enumerate selectors to verify
  the promise. Selector enumeration appears only in small-instance tests.
- Both scalar shooting proofs use secant slopes in [-1,1], including equal
  coordinates (choose slope zero). No differentiability at a kink is assumed.
- Scalar roots at breakpoints and any number of zero solution coordinates
  are permitted. The sign recovery proof needs a gap only for nonzero true
  coordinates. Tests include zeros and very small nonzero rational values.
- The root bound and nonzero-coordinate lower bound are distinct Cramer
  consequences. D is allowed to be exponential in value; only log D enters
  the iteration count. The evaluation-denominator argument bounds actual
  bit lengths rather than counting unbounded arithmetic operations.
- Zero superdiagonal entries are handled by a block lower-triangular solve.
  Its adjusted right-hand sides have polynomial bit lengths, using global
  solution-coordinate height bounds. The n=1 case is included.
- The second class requires |a_ii|>1 for the eliminated scalar equations;
  global regularity by itself does not imply this assumption.
- The cyclic determinant and Newton-cycle signs are symbolic identities.
  The convex-combination certificate uses exact positive rational weights.
  The tent-map itinerary certificate covers all sign patterns symbolically;
  finite enumeration through n=10 is a regression check only.
- The optimized-handicap proof treats 0<=a<=2 separately and examines every
  mixed-sign case for a>=2. Its lower bound quantifies over every positive
  diagonal scaling. Congruence invariance handles two-sided positive scaling.
  10,116 exact rational margin tests supplement, not replace, the proof.
- The P-LCP reverse transformation handles M-I singular by trying n+1 positive
  integer scalings. Row scaling changes u, not v; recovery is explicitly stated.

## Especially important for an adversarial verifier

Inspect the polynomial intermediate-bit bound, rather than accepting the
bisection iteration count alone. Check the exact sign-selection recovery at
zero coordinates. Check that Theorem F's Lipschitz exponent reaches n-1 and
is not confused with the different indexing in Theorem H. Review all three
case splits in the handicap upper bound, especially the endpoint-constrained
quadratic minima. Verify that the inverse-hull obstruction is not overstated
as ruling out every root-dependent separation method.

The code uses ordinary Python Fraction elimination; its exactness is tested,
but no formal proof assistant or machine-checked complexity proof was used.
Historical novelty is not certified. Downstream verification should establish
priority independently before presenting these as new published theorems.
