# TR-27 concrete geometry and uniform independence review 1

Date: 2026-09-22. Reviewer: `/root/infrastructure_audit`, independent Codex AI
reviewer of these modules. Geometry was authored by `/root/reference_review`;
Independence was authored by `/root/canonical_inventory`. I authored none of
these modules, their Algebra or IntegralImage dependencies, the frozen
Definitions, or Challenge. I authored the separate ProjectiveGeometry module,
which is not imported here. This is independent module review, not an
independent final review of the whole package or external human peer review.

**Verdict: APPROVE** the exact frozen `homogeneous_parameter_semantics`,
`witness_admissible` and `eight_point_independence` declarations, with all local
helpers, at the following hashes. No mathematical or source change is requested.

## Reviewed boundary and source identity

I read Geometry and Independence completely, their entire Algebra and
IntegralImage dependencies, the relevant Definitions and Challenge signatures,
the frozen target, both author reports and evidence records, and the original
manuscript's tangent-polynomial, projected-curve and uniform-independence
arguments. I checked the actual Mathlib projective-independence definition
and its equivalence with linear independence of chosen representatives.

SHA256, paths relative to the TR-27 draft directory:

| Input | SHA256 |
| --- | --- |
| `NLA/TR27/Geometry.lean` | `4f067416b429e37e0b34a24d764cc75d895ca7b6bcbfb20c42edd8f5c2809472` |
| `NLA/TR27/Independence.lean` | `e7394b4445160b14a7754d3d234d43abb1e90d43eed288c32e38c892ad179b0e` |
| `NLA/TR27/Algebra.lean` | `ce5694407e1e40b201746dc52897ea05acbb69c27efa6c79bfb700fe070d5134` |
| `NLA/TR27/IntegralImage.lean` | `72e1d5af05acc5e7497d1db2f81d6c3585497a76bdcc4577eea6c2efa783bd89` |
| `NLA/TR27/Definitions.lean` | `5f9cbf71a854a8a8a968ea4713c12bf501726e294ed7cccacff390dafb687056` |
| `Challenge.lean` | `158b0f5d8eb23a3165caecf7ceed5c3f6ab87310c0576bbe9f57cbe3cfbe0ee5` |
| `NUMERICAL_TARGETS.md` | `409ce7140efd7b6bab005968d5af6ef28df6f795d79276919acf408d62edca52` |
| `reviews/geometry-independence-referee-1-evidence/BoundaryAndAxioms.lean` | `af763ae6069cba42dc5fc7b1f166ca6b4e47c4513725a41ed899606d11671657` |
| `reviews/geometry-independence-referee-1-evidence/typecheck.log` | `7939db18b758320741459cde2fc9f624258184c441ae313c4020eab755c04aef` |
| `reviews/geometry-independence-referee-1-evidence/evidence.json` | `2a0e16345ac1162996296b99a1f8c2dbc43ce28479b75574981e09a6c4419bba` |

The evidence JSON additionally binds the author evidence, reviewer driver,
statement freeze and retained audit-development error. No frozen mathematical
file, canonical original statement or permanent problem ID was edited here.
The published source base remains `54f93060c0c4e5dab81096c6496e0d2b4251f3ef`.

All three required signatures match the frozen statements up to ordinary
bound-variable naming. The independent audit supplies the actual implemented
proofs at verbatim Challenge types, without importing Challenge. These modules
contain no placeholders, custom axioms, implementation overrides or native
decision shortcuts. The requested George Stepaniants name and Caltech
department affiliation are present without a contact email; the original
counterexample remains attributed to Matthew J. Colbrook. The author records
identify the AI proof authors and distinguish author evidence from review.

## Concrete algebraic geometry

Every homogeneous coordinate has degree twelve: the first monomial has
degrees `12-j` and `j`, with the proved bound `j ≤ 12` justifying natural
subtraction, and the second has degrees eleven and one. If the homogeneous
map vanishes, its exact quadratic identity reduces to `85*(s^12)^2 = 0`.
Over Complex this forces `s = 0`; the last coordinate then forces `t = 0`.
The zero parameter maps to zero by the proved homogeneous scaling identity.
This proves basepoint freedom on every projective chart, including infinity.
The complete scalar range equality is supplied by IntegralImage, which uses
both charts and complex twelfth roots, not a finite parameter set.

Homogeneity of the actual substitution kernel is proved rather than assumed.
A homogeneous polynomial of degree `n` substitutes to one of degree `12*n`.
Expanding an arbitrary polynomial into all its homogeneous components and
taking component `12*n` of its substituted value recovers exactly the
substitution of component `n`; distinct input degrees cannot collide because
multiplication by twelve is injective on natural degrees. Components above
the original total degree are explicitly zero. Thus a polynomial in the
kernel has every homogeneous component in the kernel.

The kernel is prime because the target parameter polynomial ring is an
integral domain, and its quotient is therefore reduced. Nonemptiness is
witnessed by the actual nonzero vector `curve (some 0)`. For nondegeneracy,
the thirteen source vectors at exact parameters `0,1,...,12` form a basis
by the general Vandermonde determinant criterion and dimension equality.
The proven surjective quotient carries their span onto all twelve target
coordinates. Their images all belong to the complete cone. This finite basis
is sufficient for span; it is not being substituted for the whole variety
in any rank or independence assertion.

The reviewed whole-image dependency is substantive: the integral polynomial
substitution and maximal-ideal lying-over, followed by the Complex-point
Nullstellensatz, show that every zero of the kernel ideal has a homogeneous
parameter preimage. Therefore `witness_admissible` concerns the full algebraic
zero locus, with no unexamined extra closure points or conjectural geometric
assumptions. Smoothness and the source's stronger general-delay theorem are
not asserted by these auxiliary declarations and are not required by the
canonical counterexample target.

## Uniform independence, zero and infinity

`coefficientFunctional` pairs the first thirteen polynomial coefficients with
the source vector. For degree at most twelve it evaluates the polynomial at
every finite parameter; at infinity it returns coefficient twelve. These are
exact identities over Complex.

For any list of at most eleven proposed tangent terms, `tangentPolynomial`
is `X` times factors `X-a` for the finite nonzero entries. Entries equal to
zero or infinity contribute the factor one. Repetitions are allowed. The
coefficient of `X` is a product of nonzero constants, so it is nonzero. The
degree is at most `k+1`; if infinity occurs, one factor is one and the sharper
bound is `k`. Consequently the coefficient functional annihilates every
proposed curve vector, including infinity, but not the tangent vector `e_1`.
This excludes a span expression with arbitrary complex coefficients, including
zero coefficients and the empty list. There is no positivity or distinctness
assumption in this exclusion.

For a distinct family of at most eight source parameters, a separating
polynomial for a selected finite parameter vanishes at every other finite
parameter and is nonzero at the selected one. Its degree is at most eight,
so it annihilates infinity as well. Applying its functional to a linear
dependence forces each finite coefficient to vanish. At most one infinity
entry remains by injectivity, and its coefficient vanishes by the last
source coordinate. This covers finite zero, all complex values, infinity,
and the empty family uniformly.

If the center were in the span of eight proposed source points, adjoining
the fixed three points at `1,2,3` would place `e_1` in the span of at most
eleven source points. The append construction permits overlap with the
original list, and the tangent exclusion already permits repeated entries.
The center is therefore outside that span. Together with the exact
one-dimensional quotient kernel, this gives disjointness from the kernel
and hence preservation of the source family's linear independence under
projection.

The final step applies to every point of the algebraic variety. The whole
cone equality provides a finite or infinity parameter for any projective
representative; its zero alternative is excluded by `rep_nonzero`, and the
nonzero scalar is absorbed by actual projective equality. An injective
projective family has distinct chosen parameters, since equal parameters
would yield equal projective points. This needs no assumption of global
injectivity of the parametrization. Mathlib's actual `Projectivization.Independent`
constructor then gives the frozen `eight_point_independence` conclusion.
The theorem is about the whole variety, not generic points, a dense subset,
one affine chart, or a numerical sample.

## Independent execution and remaining limits

Running
`python3 reviews/geometry-independence-referee-1-evidence/typecheck.py`
from the TR-27 directory freshly elaborates Definitions, Algebra,
IntegralImage, Geometry, Independence and the independent boundary/axiom
audit into `/private/tmp/nla-tr27-geometry-independence-referee-1-fresh`.
The final six runs exit zero without warnings. The exact Challenge-type
examples elaborate, and all 39 public definitions/theorems in the two
reviewed modules print exactly `[propext, Classical.choice, Quot.sound]`
as their transitive axioms. The final source hashes equal the pre-review
frozen hashes.

An initial reviewer-created audit example omitted the explicit arguments to
`eight_point_independence`; the audit therefore failed after all five actual
source modules had compiled successfully. Only that reviewer audit expression
was corrected. The original log is retained, and the complete final run
passes. This was an audit-harness application error, not a source-proof
defect or a changed mathematical boundary.

The compiler is Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, using the existing macOS package
cache recorded by the driver. These are development checks, not authenticated
Linux sandbox replay, LeanCert kernel-trust assertions or Comparator results.
The all-target package still needs those gates and independent review of
the remaining proofs. This review neither certifies the full original
TR-27 counterexample nor authorizes a Lean-verified status promotion.
