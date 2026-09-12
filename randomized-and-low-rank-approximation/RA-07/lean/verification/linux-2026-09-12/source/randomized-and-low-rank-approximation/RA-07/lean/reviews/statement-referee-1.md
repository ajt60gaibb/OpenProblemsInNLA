# RA-07 independent statement referee 1 — APPROVE

Date: 2026-09-12. Reviewer: OpenAI Codex agent `/root/formal_review_standards`.
I did not author the RA-07 statements or implementation. This is independent
statement/fidelity review, not proof review, external human peer review,
source-author endorsement or Linux Comparator verification. No source correction
is required. A second independent approval is required before implementation.

## Exact reviewed boundary

I read the full canonical README, complete Colbrook manuscript including its
applications and scope, historical review, Definitions, Challenge, numerical
targets, source map and metadata. Freeze:
`ef989bac80cf7a9c671557ff45305b56a7f4d11701bbcb44336a5a1448e8c803`;
base: `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.

| Reviewed file | SHA-256 |
| --- | --- |
| `NLA/RA07/Definitions.lean` | `5eb47e2450eefe5a83e583173ac1de48c67be502a73f52cb4856a26c3fffb9ff` |
| `Challenge.lean` | `013fe0fd10b21a4e09260ea07477f8b6314e36df8cad9863274b486115de20cf` |
| `NUMERICAL_TARGETS.md` | `d608c6dd1b09a0c3425c740ca159bb317a4b5079dd4d128ad52239af6f8b4dcc` |
| `SOURCE_MAP.md` | `5740574514085cc47c6657285b49074ada0ae8011c387fc983aeb12021d7ff12` |
| Canonical RA-07 README | `895569df92c91c035ba57817b1e833a4369072bb73c550bd8c79f7890d02d11d` |
| Complete Colbrook manuscript TeX | `12d83b342f9f069cf1a623b4dffe6ee6d6abb1c5d0a9d001f4713777b5beef01` |

All frozen source, configuration, documentation and author evidence hashes matched
before and after review. Complete informal sources match their Git blobs. All ten
dependency revisions match the manifest and their tracked worktrees are clean.
Raw commands, actual type inspection and integrity records are retained in
[statement-referee-1-evidence](statement-referee-1-evidence/).

## Canonical fidelity and actual definitions

The final assertion retains every `n≥3`, every strictly positive real tuple,
and every `2≤j≤n−1`. There is no sorting, distinctness, normalization, numerical
cutoff, fixed dimension, generic-position or preassigned root hypothesis. The
weak inequality includes equality for all-equal spectra. Factorization and
real-rootedness are conclusions of unconditional exports, not assumptions added
to the canonical theorem.

`elementarySymmetric` is the actual sum over subsets of size `j`. I inspected
`Finset.powersetCard` and its membership theorem: membership is exactly subset
containment plus cardinality equality. Zero-based Fin coordinates only relabel
subsets. Ordinary real division is used for the original ratios. The elementary
values export derives the empty and oversized subset conventions and positivity
of every used denominator. At the upper endpoint the final ratio is `F_n=0/e_n`
with `e_n>0`; no totalized `0/0` is used in the canonical range.

The generating polynomial is the actual product of `1+lam_i X`, and derivatives
are actual iterates of `Polynomial.derivative`. Its coefficient/factorial bridge
is an obligation for every natural index, not a definition chosen to make the
claim hold. The positive-factorization export requires exact polynomial equality,
positive scale, exact degree `n−d` and exactly `n−d` factors. It therefore retains
all repeated-root multiplicities. At `d=n` the derivative is a positive constant
with an empty factor family; the auxiliary `n=0,d=0` case is also consistent.

The second difference at `j` uses derivative order `d=j−1`, hence factor count
`m=n−j+1≥2`. At `j=n−1`, `m=2` and the third derivative vanishes. At `n=3` the
only index is `j=2`, precisely this endpoint. Natural subtraction cannot truncate
an admissible index incorrectly. No nonconstant-root theorem is required of the
constant derivative at `d=n`.

## Independent mathematical reconstruction

Expansion at zero gives the first three normalized derivative values as `s1`,
`s1²−s2` and `s1³−3s1s2+2s3`. The factorial bridge therefore identifies the
three actual ratios with `s1`, `(s1²−s2)/s1`, and
`(s1³−3s1s2+2s3)/(s1²−s2)`. Their second-difference numerator over
`s1(s1²−s2)` is exactly `2(s1s3−s2²)`.

The strict Fin order in `pairGap` counts each unordered pair once. Pairing
opposite off-diagonal terms gives
`s1s3−s2² = Σ_(a<b) μ_a μ_b (μ_a−μ_b)²`, with no missing factor two.
Also `s1²−s2 = 2 Σ_(a<b) μ_a μ_b > 0` for at least two positive entries.
The gap is nonnegative rather than necessarily positive. The degree-two endpoint
has a zero third derivative and still satisfies exactly the same certificate.

The proposed Gauss–Lucas route is mathematically appropriate: the strictly
negative real axis in the complex plane is convex, and the actual theorem uses
convex hull, not closure. Root-set inclusion alone does not establish the full
multiplicity or degree; the frozen factorization export correctly requires both.

**Implementation caution, not a statement defect:** the inspected Mathlib
`Polynomial.natDegree_iterate_derivative` proves only an upper bound. Exact degree
`n−d` also needs the nonzero leading coefficient/characteristic-zero argument.
The author and parent were informed. Complex splitting, all root multiplicities,
strict negativity and descent to real factors must likewise be proved, rather
than inferred from root-set containment alone.

## Fresh compilation, trust and diagnostics

Definitions and Challenge were re-elaborated from their actual source into a
fresh separate prefix, with the author's project build directory excluded from
`LEAN_PATH`. Both commands and a separate declaration/API inspection exited zero.
Definitions had no warnings; Challenge had exactly six deliberate placeholder
warnings. All eight actual definitions passed LeanCert `#assert_trust kernel`;
all eight transitive axiom reports contain exactly `propext`, `Classical.choice`
and `Quot.sound`. All six Challenge declarations intentionally contain `sorryAx`:
they prove nothing. There is no Proof or Solution module. This local macOS check
reuses pinned dependency artifacts and makes no fresh-Linux verification claim.

An independently written exact rational diagnostic checked 127 tuples, 392
canonical second differences, 120 upper-endpoint cases, 20 all-equal zero second
differences and 124 independent positive-mu pair certificates. It compared literal
subset enumeration with product coefficients, differentiated coefficient lists,
and checked factorial identities, exact degrees, ratio bridges, denominator signs
and the pair factor two. Empty auxiliary dimensions, repeated values and degree-two
endpoints are included. These finite checks do not prove universal factorization,
convexity or any Lean theorem.

The analytic computation plan is appropriate for this universal affirmative
result. There is no numerical witness requiring an interval search. An artificial
point certificate would add no mathematical assurance; actual LeanCert kernel
trust audits remain relevant. Any later numerical certificate must be independently
reviewed and actually consumed by the final proof. The six exact exports and
standard-three-axiom whitelist are fixed, with no replaceable definitions.

## Scope and final gate

The source's strict monotonicity, extra index-one assertion, determinantal sampling
identity and Jensen/stable-rank corollaries are explicitly excluded from advertised
formal results. Their exclusion does not narrow the original scalar question.
Credit remains Matthew J. Colbrook for the mathematics and George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, for formalization, without a George email.

This statement approval applies the relevant Tau Ceti-style fidelity, substantive
mathematics, API reuse, trust, endpoint and scope checks. Final proof implementation
still requires two independent final reviews, actual source re-elaboration,
no holes or additional axioms, and real Linux sandbox/Comparator/default-kernel
verification before promotion. I changed no mathematical or canonical source and
made no commit or push.
