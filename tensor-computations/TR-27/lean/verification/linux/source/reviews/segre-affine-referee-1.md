# TR-27 Segre and affine/projective bridge review 1

Date: 2026-09-22. Reviewer: `/root/infrastructure_audit`, Codex AI agent.
I did not author or edit SegreSemantics, AffineBorder, their common Semantics
dependency, Definitions or Challenge. These two proof modules were authored
by `/root`. I authored the separate ProjectiveGeometry module, which neither
reviewed module imports; this is an independent module review, not an
independent review of the entire TR-27 package or external human peer review.

**Verdict: APPROVE** the exact auxiliary declarations `segre_cone_rank`,
`segre_rank_minimum` and `projective_affine_border`, with their local helpers,
at the hashes below. No mathematical or signature change is requested.

## Exact source boundary

I read both modules completely, their transparent definitions and three
Challenge declarations, the canonical problem and frozen semantic target,
the common Semantics dependency, and the author's successful development
log. I inspected the retained Mathlib implementations of the tensor spanning,
polynomial function extensionality and coefficient lemmas used here.
The three signatures are identical to the frozen Challenge after whitespace
normalization, including every ambient type, hypothesis, rank bound and
nonzero-vector premise. Definitions and Challenge still match the statement
freeze. The source contains no added axioms or placeholders and does not
import Challenge. The required George Stepaniants attribution, Caltech
department affiliation and original Matthew J. Colbrook proof attribution
remain present, without contact email and with AI assistance disclosed.

SHA256, relative to the TR-27 draft directory:

| Input | SHA256 |
| --- | --- |
| `NLA/TR27/SegreSemantics.lean` | `d6fc909c5a41ce146aa5883f6588537d2829f60937a1b781507d8743550d4489` |
| `NLA/TR27/AffineBorder.lean` | `823403583e3b3194b8166bf86aa81afae36a0e6e047390afd0367ab269c322c9` |
| `NLA/TR27/Semantics.lean` | `d1a2e30e0cec093d276c529268d8744e5c53b04706499b58827c435cf460142c` |
| `NLA/TR27/Definitions.lean` | `5f9cbf71a854a8a8a968ea4713c12bf501726e294ed7cccacff390dafb687056` |
| `Challenge.lean` | `158b0f5d8eb23a3165caecf7ceed5c3f6ab87310c0576bbe9f57cbe3cfbe0ee5` |
| `NUMERICAL_TARGETS.md` | `409ce7140efd7b6bab005968d5af6ef28df6f795d79276919acf408d62edca52` |
| `reviews/segre-affine-author-evidence/typecheck.log` | `62c941dc4e9dc47f648ea3b132f8646cd5a8af094cbdad65c139e1e9a2049996` |
| `reviews/segre-affine-referee-1-evidence/typecheck.log` | `308a522be091cd7cb75aacaa4a1be910b920ee99d46eb734fd18e2db1c596567` |

The machine-readable receipt in `segre-affine-referee-1-evidence/evidence.json`
also binds the development driver and statement-freeze record.

## Segre decompositions and minima

The forward rank equivalence expands each projective Segre point into two
separately chosen projective points and a nonzero scalar relating its actual
representative to their tensor. Multiplying this scalar into the unrestricted
complex decomposition coefficient gives precisely the required affine tensor
sum. Left and right factors remain independent; no symmetry, distinctness,
normalization, positivity, finite parameter grid or merging of tensor modes
is imposed.

Conversely, each nonzero simple tensor gives its projective Segre point.
A zero tensor summand is assigned one fixed nonzero Segre point constructed
from the admissible cone's nonzero member. The span argument retains the
original zero summand and proves its membership using `Submodule.zero_mem`;
it does not silently attach the original coefficient to the replacement
nonzero point. Thus zero factors, zero coefficients, repetitions and
cancellation preserve the original length bound. `Represents z q` forces
`z` nonzero. A length-zero decomposition would force `z = 0`, so there is no
empty-list escape in either direction.

For existence of a finite tensor decomposition, the bilinear tensor map
carries the spans of the two cones to the span of their pairwise products.
Both cone spans are the full ambient space, and ordinary simple tensors
span the actual tensor product. Finite span membership therefore supplies
a finite list of independent factor choices. The Segre minimum proof then
uses an explicitly established nonempty length set and its monotonicity;
the natural infimum is attained, rather than being an empty-set default.

## All-polynomial Zariski correspondence

The forward implication starts with an arbitrary polynomial vanishing on
the entire coordinate image of the affine rank-at-most set. That set is
closed under every complex scalar: scaling is absorbed into its unrestricted
coefficients. The polynomial in a scalar variable obtained by evaluating at
`a • v` has the homogeneous-component evaluations as coefficients. It
vanishes for every complex `a`, and Mathlib's polynomial extensionality over
the infinite field Complex makes it identically zero. This is not finite
sampling. Coefficient extraction handles every degree, with components above
the total degree proved zero. Each homogeneous component then vanishes on
the projective rank locus, hence at the projective closure point. Summing
the components recovers the arbitrary polynomial's vanishing at the supplied
nonzero vector.

The reverse implication handles a homogeneous equation of arbitrary degree,
including degree zero. A nonzero coordinate `j` of the target vector exists
because the coordinate map is injective. Multiplication of the equation by
the coordinate polynomial `X j` produces an ordinary polynomial vanishing
on the entire affine rank-at-most set: at nonzero vectors this follows from
the projective-cone rank equivalence and representative scaling, and at the
origin the coordinate factor vanishes. The affine closure hypothesis makes
this product vanish at the target. Its nonzero coordinate factor can be
cancelled, proving the original homogeneous equation there.

This coordinate-factor argument is essential for empty projective rank
loci and degree-zero equations. At rank bound zero, the affine rank locus
contains only the origin while the projective locus is empty; the theorem
restricts to a nonzero vector, so both closure-membership assertions are
false as required. No positive-rank assumption or unjustified assertion
that every homogeneous equation vanishes at the origin is present.

Both directions use the full definitions: all affine polynomials on the
whole affine set and all homogeneous polynomials of all degrees on the
whole projective set. The bridge concerns actual Complex points and does
not replace the stated Zariski closure by a Euclidean or sampled closure.

## Independent development execution and remaining gates

I independently ran the existing development driver with modules
`Semantics`, `SegreSemantics`, `AffineBorder`, build directory
`/private/tmp/nla-tr27-segre-affine-referee-1-fresh`, and the pinned Lean 4.33.1
macOS executable at
`/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean`.
The package cache was
`/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages`.
Definitions and all three proof modules were freshly elaborated. Every step
exited zero without warnings; all three required declarations, and the
homogeneous-component helper, print exactly
`[propext, Classical.choice, Quot.sound]` as their transitive axioms.

This cached macOS development execution is not authenticated Linux kernel
replay, LeanCert trust assertion or Comparator verification. Textual signature
agreement does not replace Comparator. These three auxiliary declarations
also do not complete TR-27: the concrete witness and all remaining frozen
obligations still require their proofs and independent review before the
complete package can pass the final reproducibility and publication gates.
