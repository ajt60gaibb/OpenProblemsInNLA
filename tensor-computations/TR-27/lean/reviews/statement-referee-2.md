# TR-27 independent statement review 2

Date: 2026-09-22. Reviewer: `/root/reference_review`, independent Codex AI
agent. Phase: exact mathematical and Lean statement boundary before proofs.
This reviewer did not author or edit the TR-27 definitions, Challenge,
specification, or proof route. The draft author was `/root/canonical_inventory`.

**Verdict: APPROVE the mathematical boundary at the hashes below.** It
expresses a counterexample to the complete original universal implication,
using actual complex projective points and tensor products, and explicitly
requires the geometric, closure, minimum-rank and whole-image bridges. No
mathematical change is requested. Approval does not prove any of the 25
Challenge statements and does not certify TR-27 as Lean verified.

## Reviewed sources and byte binding

Read the complete canonical README, complete Colbrook manuscript (including
the general construction, explicit twelve-coordinate example, smoothness and
eventual-power sections), sibling target and API documents, final self-contained
numerical specification, both Lean files, Comparator configuration, package
README/metadata, and both development typecheck logs. The two original source
files were compared byte-for-byte with `git show` at published base
`54f93060c0c4e5dab81096c6496e0d2b4251f3ef` and matched.

Hashes are SHA256 of raw bytes. The first two paths are repository-relative;
the remaining paths are relative to the TR-27 draft directory.

| Input | Bytes | SHA256 |
| --- | ---: | --- |
| `tensor-computations/TR-27/README.md` | 5113 | `111ccd36436f926608d1e604ed974d82dfe9ece400c7ac2ce8710d96d00b2e00` |
| `references/colbrook-tensor-metrics-rank-2026-09-11/manuscripts/tr27_solution.tex` | 14995 | `e554971c970e05efb61675f35d66bdc4847266fe5eba86e8cb445043fb83be67` |
| `NLA/TR27/Definitions.lean` | 9046 | `5f9cbf71a854a8a8a968ea4713c12bf501726e294ed7cccacff390dafb687056` |
| `Challenge.lean` | 7967 | `158b0f5d8eb23a3165caecf7ceed5c3f6ab87310c0576bbe9f57cbe3cfbe0ee5` |
| `NUMERICAL_TARGETS.md` | 16486 | `409ce7140efd7b6bab005968d5af6ef28df6f795d79276919acf408d62edca52` |
| `../TR-27-TARGETS.md` | 13090 | `a414e74a594885283c2c9ff35b66c0752d427ddb49f1c689a8e58be514856079` |
| `../TR-27-API.md` | 18707 | `dd3475ef7074fcd97713290cfbf5da13c1ad1383166577d4abc8d567ec0b9ef1` |
| `comparator.json` | 1120 | `2cf6d47dd9b3ad53fabd80b87c49476eefebd07c930994929a8534a0d8b46291` |
| `reviews/root-statement-typecheck.log` | 1922 | `d6d74c9df7c3081fad167fe3b1d5f8b39278461e202d473060679839df43e794` |
| `reviews/statement-typecheck.log` | 1895 | `d65d9ba089b0d88998644a0236075a7880ca4291d008bc43b52e7c31fe612578` |
| `README.md` | 6462 | `d563cbd2e544f9310be92bd15d333bbb00c29f8aed24548451680d9a6e58b633` |
| `formalization.yaml` | 3676 | `01506a7002e2e0eff6404e8354a5317c7f44cc940f638c45d03a1077a7dbdb80` |

The actual definitions of Mathlib `Projectivization`, its representative,
projective span and independence, multivariate zero locus and vanishing ideal,
and integral ring homomorphism were also inspected in the extracted Mathlib
source documented by the API reconnaissance. This review does not convert
that source directory's lack of Git metadata into an independent revision
authentication claim. The pinned-compiler elaboration is separate evidence.

## Full universal target and admissible geometry

`CanonicalConjecture` quantifies over arbitrary complex vector spaces with a
finite coordinate presentation, every admissible variety, every projective
point, and its actual projective tensor square. A presentation includes a
linear equivalence with `Fin n -> Complex`, which enforces finite dimension
without a hidden bound on `n`. `finite_coordinates` requires the converse
availability of such coordinates for every finite-dimensional ambient space;
`coordinate_transport` requires preservation of admissibility and both ranks
under an actual ambient linear equivalence. Restricting the Lean universe to
`Type` in the universal proposition does not restrict the mathematical
finite-dimensional examples, all of which have the displayed coordinate
models.

`ProjectiveVariety` alone carries coordinate data and an ideal, not a claimed
answer. Its separate `Admissible` predicate requires total-degree homogeneity,
a proper prime ideal, a reduced quotient coordinate ring, a nonzero point in
the complete affine zero locus, and full linear span. These are ordinary
homogeneous-coordinate conditions for a nonempty reduced irreducible
nondegenerate complex projective variety. A prime ideal is radical; over the
algebraically closed field Complex, the Nullstellensatz identifies it with
the ideal of its whole cone. The nonzero-cone condition rules out the
irrelevant-origin case. Conversely, the homogeneous vanishing ideal of a
classical irreducible reduced projective variety is prime. No rank or tensor
conclusion is part of admissibility.

The exported `admissible_geometry` further requires actual closedness,
nonempty irreducibility under the classical closed-set union criterion, and
full projective span of the point set. Thus a proof cannot silently substitute
irreducibility of a generic prime-spectrum space for irreducibility of the
complex projective points. For a negative answer, the concrete fully admissible
counterexample already suffices for the original class; it does not depend on
using a possibly vacuous universal premise over unconstructed varieties.

`points` uses Mathlib's nonzero representative of each projective line.
Although that representative is chosen, homogeneity makes vanishing invariant
under every nonzero scalar. `cone_projective_membership` explicitly requires
this bridge for an arbitrary nonzero vector. It is not assumed as a field of
the concrete witness.

## Rank, closure and tensor semantics

`ProjectiveRankAtMost` uses the actual Mathlib projective linear span of an
arbitrary list of at most `r` points. Repetitions are permitted. A list of
length zero spans no projective point. `ConeRankAtMost` permits arbitrary
complex coefficients and cone vectors, including zero terms. Removing zero
terms and absorbing nonzero scales gives the usual equivalent projective
notion; `projective_cone_rank` requires that equivalence rather than treating
it as a convention with no proof obligation.

The two ranks are natural-number infima. `rank_minima` requires nonempty
length sets and both equivalences between the actual at-most predicates and
comparison with the infimum. Full span ensures ordinary finite rank; closure
contains the corresponding rank locus. Therefore no empty-set default may
be used to manufacture the rank inequality. `segre_rank_minimum` supplies
the corresponding nonempty minimum for the full Segre point set.

`zariskiClosure` tests **all** homogeneous complex polynomials, of every
natural degree, that vanish on the whole supplied projective set. Homogeneous
zero conditions are invariant under choice of representative. This is the
classical projective Zariski hull, not Euclidean closure or a finite collection
of selected equations. Constants of degree zero correctly ensure that the
closure of the empty projective set is empty. The affine closure uses the
zero locus of the standard vanishing ideal of the whole affine set, hence
all complex polynomials. `projective_affine_border` requires the exact bridge
for every rank bound and nonzero vector. At `r=0`, the projective locus and its
closure are empty, while the affine rank cone is `{0}`; restricting the bridge
to nonzero vectors makes both sides false, as required.

The target tensor lies in `W tensor[Complex] W`. `Represents` demands a
nonzero scalar relating an actual projective representative to the vector,
which in particular forces that vector to be nonzero. `tensor_representatives`
requires nonvanishing of a simple tensor with nonzero factors and existence
and uniqueness of its projective point. `IsTensorSquare` consequently refers
to the square of any representative up to the unavoidable nonzero square
scalar, not to an arbitrarily selected new tensor.

`segrePoints` independently chooses one point from each factor. Its affine
counterpart `TensorRankAtMost` independently chooses each left and right cone
vector, with unrestricted complex coefficients and possible repetitions.
`segre_cone_rank` requires their exact equivalence. No symmetric-decomposition
restriction, finite parameter restriction, matrix surrogate without a bridge,
or merging of tensor modes appears in the original-target proposition or its
concrete counterexample.

## Exact witness and full algebraic image

The coordinate index map sends `Fin 12` to `0,2,3,...,12`, skipping precisely
the exponent-one coordinate. The source curve includes every complex finite
parameter and the infinity vector `e_12`. The quotient map is exactly
`5*w_j-S_j*w_1`, where `S_j=1+2^j+3^j`; its center has coordinate one equal
to `-5`. Its selected columns give `5I`, and the declared kernel is the span
of that actual center. `quotient_semantics` requires linearity, surjectivity
and this kernel equality, all without hypotheses supplying them.

The twelve witness coordinates were independently recomputed by integer
arithmetic and match the source:

```text
-3, -14, -36, -98, -276, -794, -2316, -6818,
-20196, -60074, -179196, -535538.
```

Each homogeneous coordinate has total degree twelve. The natural subtraction
in `12-coordinateIndex j` is harmless because that index is always at most
twelve. `homogeneous_parameter_semantics` requires base-point freedom and
equality of the **entire** homogeneous range with the scalar cone of all finite
parameters and infinity. Complex twelfth roots account for every nonzero
scalar, so this range equality is mathematically the appropriate one rather
than an unjustified identification of a projective image with one affine chart.

`witnessIdeal` is the actual kernel of substitution into these homogeneous
polynomials. It does not define the witness as an assumed parameter set with
the word "closed" attached. `whole_closed_image` requires both directions of
the equality between its entire zero locus and the homogeneous range, and
then equality with the complete parameter cone. Extra algebraic closure
points therefore cannot be silently omitted from the lower bounds.

The proposed integral-map route is mathematically concrete. With
`a=s^12`, `b=s^11*t`, one has `H_0=5a-3b` and
`a*H_2=5b^2-14ab`. Substitution and expansion give

```text
85*a^2 + (8*H_0+9*H_2)*a - 5*H_0^2 = 0.
```

In `integral_quadratic`, Lean coordinate index 1 is exponent label 2, so the
signature uses precisely this identity. Division by the nonzero constant 85
gives a monic equation for `s^12`; then `(5a-H_0)/3` gives `b`, and
`(H_12+535538b)/5` gives `t^12`. Integrality passes to `s` and `t` from their
twelfth powers and hence to the entire polynomial ring. The integral map plus
lying over and the complex Nullstellensatz supplies the proposed exhaustive
zero-locus image route. These are substantial unproved tasks, but they are
correct statements, and `substitution_integral` and `whole_closed_image` require
them unconditionally. No chosen output chart, nonzero-coordinate division,
or selected subset of the image narrows these obligations.

## Lower bounds and original-target negation

`eight_point_independence` quantifies over every injective family of at most
eight points of the whole witness variety. Mathlib's projective independence
has the intended equivalent meaning for any nonzero representatives. The
statement includes the empty family without introducing a generic-position
condition or selecting only the three convenient source parameters.

`witness_three_terms` requires a nonzero target, its exact three-term
expression, and impossibility of any at-most-two-term cone expression.
`border_curve_semantics` uses the polynomial extension with constant first
coordinate `-3`; it is nonzero even at zero, specializes there to the witness,
and agrees with the divided difference for all nonzero parameters.
`border_two` is explicitly membership in the all-polynomial affine Zariski
closure. Thus a mere limiting expression does not by itself discharge the
border-rank obligation.

`square_nine_terms` uses the genuine tensor expansion over parameters 1, 2
and 3. `square_not_eight` excludes all short expressions over the entire
cone, allowing repeated points, arbitrary complex scalars and unrelated
left/right factors. Together with the Segre and minimum bridges, these give
rank exactly nine, not just failure of one proposed eight-term decomposition.

The final `projective_counterexample` assumes none of the geometry or rank
lower bounds. It asserts admissibility and actual points with rank 3, border
rank at most 2, and square rank 9. Since `2<3` and `9=3^2`, these values
contradict exactly the strict conclusion of the universal implication.
`original_conjecture_false` then states its full negation. Exact border rank
two, smoothness, arbitrary finite delays and eventual-power saving are
optional source strengthenings; omitting them does not weaken the negative
answer required by the complete canonical problem. Their omission is disclosed,
and the original source and problem statements remain intact.

## Typechecking, metadata and limits

The two inspected logs show Lean 4.33.1 on macOS, successful Definitions
elaboration and successful Challenge elaboration with 25 expected deliberate
placeholder warnings. The root log records a separate external build from
the author log. This agent inspected those logs and did not personally rerun
Lean. Typechecking establishes neither the statements' truth nor a permitted-
axiom proof audit: every Challenge proof remains a placeholder.

The future Comparator configuration lists all 25 declared obligations,
including both final targets and the semantic/image bridges, leaves
`definition_names` empty, and permits only `propext`, `Classical.choice`,
and `Quot.sound`. There is no existing Solution or successful Comparator run.

The final inspected metadata uses `repository.role: substantive-development`
and passed an independent schema-only validation against the retained v0.4
schema using the available PyYAML/jsonschema interpreter. Its scope remains
statement-only with no claimed completed target, axiom pass, or authoritative
Linux result. This resolves the earlier packaging issue reported by the root
with the invalid `statement-draft` role value; no mathematical signature
changed. Metadata and README still mark independent review pending at this
snapshot, which can be updated after both signed reports are retained.

Original mathematical attribution remains Matthew J. Colbrook; formalization
credit and the requested Caltech affiliation remain George Stepaniants, without
a new contact email. AI assistance and the author's inability to count as an
independent referee are explicit. This report is an independent AI statement
review, not human peer review, a proof of the 25 obligations, or endorsement
by Tau Ceti. Material mathematical changes after this approval require renewed
independent review before substantive proofs use the changed boundary.
