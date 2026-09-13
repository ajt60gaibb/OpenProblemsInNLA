# RA-07 independent final proof referee 1 — PASS

Date: 12 September 2026. Reviewer: OpenAI Codex agent
`/root/leancert_examples`, independent of RA-07 implementer
`/root/solved_statement_inventory`. **Approve the completed six-export
formalization at the exact frozen bytes below. No mathematical correction is
required.** This is independent AI-agent proof and scope review, not external
human peer review, official Tau Ceti endorsement, or Linux Comparator execution.

I read the complete canonical README, the complete Colbrook manuscript including
its later applications and scope, the full definitions and Challenge, numerical
targets and source map, every implementation module and Solution, both statement
approvals, and the actual relevant pinned Mathlib and LeanCert APIs. I independently
re-elaborated all seven project source modules and a separate inspection module.
I did not alter any mathematical source, canonical page, dependency, or prior
review. All 41 files bound by the proof freeze, including its three original
source files, remained unchanged throughout this review.

## Exact boundary and implementation

Proof freeze: `ecd94daf2dee9fe4625e09f1a08026eb75ac8a14bea6efb688921a3e78eb6b4a`.
Completion report: `c80547f6d812d879d7e7d9d7ed05c089146b6e0ad3a208c27d3b666b49981689`.
Canonical source revision: `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.

| File | SHA256 |
|---|---|
| `NLA/RA07/Definitions.lean` | `5eb47e2450eefe5a83e583173ac1de48c67be502a73f52cb4856a26c3fffb9ff` |
| `Challenge.lean` | `013fe0fd10b21a4e09260ea07477f8b6314e36df8cad9863274b486115de20cf` |
| `NUMERICAL_TARGETS.md` | `d608c6dd1b09a0c3425c740ca159bb317a4b5079dd4d128ad52239af6f8b4dcc` |
| `NLA/RA07/Algebra.lean` | `1be33b680d0f66d793a564ec22aae8996474aa85f7699f4d1dff6639903cf013` |
| `NLA/RA07/Roots.lean` | `ccbb931696ed1fafcda2518daaccee8eacb201a10eaedefd694f573b44adecde` |
| `NLA/RA07/Sums.lean` | `6a1410ed2efe6155f2f27c22b8afe37ffd0110812850f0d336c9ffee2dd8050b` |
| `NLA/RA07/Proof.lean` | `20c4d2a1078495b442f74126b42e0960462a1e82e3c5aec0b2c09065921dd21d` |
| `Solution.lean` | `55ea9b34825481eb10fefc6409eab16db61849663849f2ca09f6ceb8a1857114` |

Both statement approvals predate the recorded proof start and bind these
unchanged statements. The six public Solution signatures are verbatim equal
to Challenge's six signatures; Comparator selects exactly those six and leaves
`definition_names` empty. Source and configuration identity is recorded in the
new [referee evidence](../verification/final-referee-1/).

## Complete target and definition fidelity

`ConvexityConjecture` retains every natural `n≥3`, every strictly positive real
tuple `lam : Fin n → ℝ`, and every original `2≤j≤n−1`. Its conclusion is the
weak second-difference inequality for `(j+1)e_(j+1)/e_j`. There is no fixed
dimension, bound or normalization on the entries, sorting, distinctness,
generic-position condition, assumed factorization, or assumed certificate.
The all-equal case may have zero second difference, so weak convexity is correct.

The actual `Finset.powersetCard` membership theorem requires exactly a subset
and the specified cardinality. `elementarySymmetric` sums the products over
these genuine subsets once each. Real multiplication, real division, and natural
powers were confirmed by fully explicit elaboration. Zero-based Fin labels only
relabel the original subsets. `generatingPolynomial` is the actual polynomial
product, and `iteratedGeneratingDerivative` is actual repeated polynomial
differentiation; no surrogate coefficient or derivative object is substituted.

The formal scope is the complete original scalar question. The longer manuscript's
strict monotonicity, extra convexity index one, determinantal expectation identity,
Jensen consequence, and stable-rank estimates are explicitly outside the six
advertised exports. Their exclusion does not omit any case of the retained
canonical conjecture. Future publication wording must maintain that distinction.

## Exact algebra and all derivative roots

`elementary_values_proved` derives `e_0=1`, vanishing for every index above `n`,
and strict positivity for every index through `n` from the literal subset sum.
For admissible indices the required subset family is nonempty and each product
is positive. The empty auxiliary dimension is consistent. Thus the original
denominators and the endpoint value `F_n=0` are consequences, not defaults
chosen to force the inequality.

`generating_coeff` expands the actual product using Mathlib's `Finset.prod_one_add`;
each subset contributes its product times `X` to exactly its cardinality power.
Coefficient extraction selects the exact required subsets. This proves the
identity for arbitrary real tuples and every natural coefficient index.
`coeff_iterate_derivative` then gives the actual derivative value `j!e_j`.
`error_as_derivative_ratio` cancels only the proved nonzero real factorial.
It remains valid even at zero numerators; no division by an unproved nonzero
elementary sum is hidden in that general algebraic bridge.

`generating_natDegree` proves each factor has degree one using its positive,
hence nonzero, slope and applies the domain product-degree theorem. The exact
iterated degree comes from repeated use of Mathlib's characteristic-zero
`natDegree_derivative`, not the weaker upper-bound theorem. This resolves the
specific caution in the statement reviews.

For any actual complex root of the mapped generating polynomial, a factor
vanishes. Its positive real coefficient forces zero imaginary part and strictly
negative real part. The set `{z : ℂ | z.im=0 ∧ z.re<0}` is proved convex,
including the zero-weight cases. The inspected Mathlib Gauss–Lucas theorem uses
the convex hull itself, so strict negativity is retained without a closure
argument. Before each induction step the code proves that the preceding
derivative has positive degree. It never applies the nonconstant theorem to
a constant polynomial.

The factorization then uses actual complex splitting, proves every complex root
is in the real embedding's range, and descends splitting through
`Polynomial.Splits.of_splits_map`. It uses the **full root multiset** through
`Splits.eq_prod_roots`, `Splits.natDegree_eq_card_roots`, and `Splits.roots_map`.
The multiset-to-list enumeration preserves length and every repeated occurrence;
it does not enumerate a root set of distinct values. Strictly negative roots
give positive `μ_a = −(r_a)⁻¹`, with their nonzero denominators justified.
Each linear factor is converted algebraically and evaluation at zero determines
the precise normalization constant. Thus the factorization has exactly `n−d`
positive factors and equality of actual real polynomials.

At `d=n`, the derivative is a positive constant, its root multiset and Fin tuple
are empty, and the product is one. The auxiliary zero-polynomial factorization
helper is also valid: zero leading coefficient and the empty product give zero.
The relevant derivatives are separately proved to have strictly positive value
at zero, so this total case cannot make the final theorem vacuous.

## Pair identity, denominator, and original endpoints

`finite_product_derivatives` proves all three actual derivatives of an arbitrary
finite product by finite-set induction and the polynomial product rule. No
distinct-root or degree-at-least-three hypothesis is introduced. Its exact
expressions are `s1`, `s1²−s2`, and `s1³−3s1s2+2s3`.

`sum_strict_upper_half` splits a symmetric double sum into the two strict-order
halves and removes the zero diagonal. This checks the factor of two rather than
assuming it. Expansion then gives exactly

\[
s_1s_3-s_2^2=\sum_{a<b}\mu_a\mu_b(\mu_a-\mu_b)^2,
\qquad s_1^2-s_2=2\sum_{a<b}\mu_a\mu_b.
\]

For `m≥2` and positive entries, the actual indices zero and one supply a strictly
positive pair product. Every remaining pair product is nonnegative, and `s1>0`.
Therefore the denominator `s1(s1²−s2)` is strictly positive. The gap is merely
nonnegative and may vanish, as the target requires. Fin's genuine strict order
ensures each unordered pair is counted once.

`shifted_error_ratio` differentiates the actual factorization further, using
iteration addition and actual differentiation of a constant polynomial factor.
Its cancellation hypothesis is supplied by the already proved positive scale.
For original index `j`, `second_difference_certificate_proved` takes exactly
`d=j−1` and `m=n−(j−1)≥2`. The three shifted ratios are the actual original
ratios at `j−1`, `j`, and `j+1`. Clearing only the proved nonzero factors in
the denominator gives the stated second-difference identity. Finally, positivity
of the denominator and nonnegativity of the pair sum prove the full inequality.

At `j=n−1`, `m=2`; the generic third-derivative formula remains valid and
vanishes for the actual degree-two polynomial. The denominator remains positive
and the final ratio is `F_n=0`. This includes the only canonical index for
`n=3`. Repeated and all-equal entries are retained without perturbation or an
exceptional set. No natural-number subtraction truncates a relevant index.

As an independent supplementary check, an exact Fraction script reconstructs
subset sums, product coefficients, factorial-scaled derivatives and degrees
for eight targeted tuples, including empty/constant auxiliary cases, repeated
entries, unequal rational entries, and all-equal tuples. Four independent positive
`μ` tuples check both pair identities and the complete scalar certificate.
For `lam=(1,2,3)`, `j=2`, it independently obtains gap `13/33`, factor-certificate
gap `13/3`, denominator `22`, and zero third derivative. These finite diagnostics
support the review; the Lean proof, not those examples, establishes universality.

## Independent execution and trust

I freshly elaborated Definitions, Algebra, Roots, Sums, Proof, Solution, and the
separate Challenge into a new `.verification/ra07-independent-final-referee-1-*`
prefix. The author's `.lake/build/lib/lean` was explicitly excluded from
`LEAN_PATH`. All seven commands and the additional independent inspection
returned zero. Implementation modules emitted no warnings; Challenge emitted
exactly its six intentional placeholder warnings.

The independent inspection traversed all six exports through **62 actual project
declarations**. It checked that 18 specified substantive mathematical dependencies
are present in the actual retained proof graph, including Gauss–Lucas, exact
degree and coefficient theorems, root splitting/cardinality/mapping, both pair
identities, finite-product derivative formulas, and the true shifted-ratio bridge.
These are participating dependencies, not unused declarations placed beside
an unrelated proof.

The 12 source kernel assertions and transitive axiom reports passed, and the
inspection independently repeated all six public checks: **18 successful checks
for 12 distinct declarations**, each with exactly `propext`, `Classical.choice`,
and `Quot.sound`. All ten actual dependency checkouts are clean at their locked
commits. No implementation file contains a proof hole, custom axiom,
`native_decide`, unsafe declaration, or import of Challenge. Both implementation
entry points explicitly select LeanCert kernel trust.

I inspected the actual LeanCert `#assert_trust` implementation: it collects
transitive axioms, rejects `sorryAx` and custom axioms, and rejects native
compiler dependencies in kernel mode. Here LeanCert supplies that trust audit
for a fully analytic and algebraic theorem. There is no interval calculation,
floating-point root inference, numerical sample grid, or claimed numerical
LeanCert certificate. This agrees with both approved statement reviews and
the shared policy against decorative interval calculations.

This run used Lean 4.33.1 on macOS with existing matching dependency artifacts.
It did not rebuild Mathlib from scratch and did not run the real Linux sandbox,
Comparator export matching, or separate default-kernel replay. Those are later
operational gates and are not inferred from this PASS.

## Evidence, reuse, and remaining publication gate

Exact commands, artifact and source hashes, raw module logs, all axiom reports,
dependency pins, actual semantic/dependency inspection, exact diagnostics, and
before/after identity checks are in
[verification/final-referee-1](../verification/final-referee-1/). The new
`fresh_check.py` and `Inspect.lean` explicitly credit the existing review and
author driver patterns they adapt; their checks were independently executed.
The relevant library files and the inspected API scopes are hash-bound in
`library-source-hashes.json`.

This applies the relevant pinned Tau Ceti-style correctness, statement fidelity,
scope, endpoint, proof-quality, reuse, API, and attribution checks. Mathlib
reuse is substantive and appropriately avoids a new root-counting or numerical
root-isolation implementation. Mathematical authorship remains Matthew J.
Colbrook; formalization authorship is George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology, with AI assistance
and without his email.

The canonical status remains `Solved`. The historical stage-one package README
and publication metadata still need the planned packaging update, and actual
Linux verification remains pending. A second independent final proof approval
and the operational gates are separate requirements before promotion. I made
no mathematical edit, status change, commit, push, or PR.
