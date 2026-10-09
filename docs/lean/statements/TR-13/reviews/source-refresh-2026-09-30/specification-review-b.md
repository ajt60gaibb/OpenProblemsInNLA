# TR-13 specification source-refresh review B

Reviewer: `/root/refresh_tr13_review_b`, OpenAI Codex AI agent (`is_ai: true`).
Date: 30 September 2026 (UTC). Verdict: **approve** for the bound inputs below.

This is an independent source-refresh re-review of an already implemented
statement. I am distinct from the recorded author `/root`. I did not author
the specification or Lean definitions. This report does not claim to be a
preimplementation review or to establish new Lean or Linux Comparator results.

## Source correspondence and provenance

I read the complete current canonical TR-13 README, its complete ORIGINAL.md
snapshot, the complete numerical specification, and the archived prior source,
specification and metadata. The canonical README and current ORIGINAL.md are
byte-identical. A direct comparison with previous-original.md shows precisely
a 30-line formalization notice inserted before `## Statement`. The original
question, definitions of the five ranks, odd-order and dimension bounds,
resolution, attribution and Solved status remain unchanged. The new notice
expressly leaves separate proof-project Linux verification and final reviews
pending; this review does not certify that proof project.

The sole specification edit clarifies the provenance paragraph above
`## Exact target`: the old hash belongs to the preserved preimplementation
snapshot, while ORIGINAL.md now contains the current canonical source. The
entire mathematical specification beginning at `## Exact target` is unchanged.
Historical approvals remain historical, with their old bound source bytes
preserved. These new approvals reopen the source correspondence gate honestly.

## Mathematical fidelity

The specification retains every odd natural order m >= 5, every n >= 2, the
complex coefficient space of dimension m(n-1)+1, and the zero-based Hankel
index sum equivalent to the source's one-based sum minus m. Its actual
ordinary and symmetric decomposition descriptions encode all complex factors
and scalar-weighted pure powers, without real, positivity or structural
restrictions on ordinary factors.

Vandermonde vectors use homogeneous nonzero pairs (a,b), including either
coordinate separately zero. This retains the point at infinity; zero
coefficients retain padding. Both border widths use sequences and ordinary
complex entrywise convergence. Ordinary approximants range over the entire
ambient tensor space; symmetric approximants need only have symmetric
width, without a Hankel restriction.

All four comparisons to ordinary width are required at every natural
threshold, including zero. Padding makes each width predicate upward closed;
finite decompositions exist by ordinary tensor-product spanning, symmetric
pure-power spanning over C, and binary-power/Vandermonde spanning of the
Hankel coefficient space. Constant sequences give finite border widths.
Consequently the thresholds express equality of the five minimum ranks.

The existentially chosen polynomial is on the full coefficient space, with
an explicit nonzero-evaluation witness after m,n and before the universal
coefficient-vector condition. Its nonvanishing locus is a nonempty principal
Zariski open. Every nonempty affine Zariski open contains such a locus, so
this is equivalent to the original existence question, not a finite sample
or a claim for every exceptional tensor. The displayed generic rank formula
is source background and resolution information; the original target asks
equality of the five ranks, which this specification retains completely.

## Limits

No blocker remains in this source-refresh specification. Approval concerns
mathematical statement fidelity and exact provenance. It proves no tensor
rank theorem, runs no Lean command, promotes no catalog status, and implies
no human review or source-author endorsement.

## Reviewed input SHA-256 bindings

- `docs/lean/statements/TR-13/NUMERICAL_TARGETS.md`: `8238e5adadcc23223017e7900a751f9cd0318b5375886b5543b4b8eb9303d91d`
- `docs/lean/statements/TR-13/ORIGINAL.md`: `fa34e46c5869e28c9f198a1aa78a4a5e026ba99dcbe67ce10d3410e426f7f70b`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/README.md`: `abd6d3efd86f6431f3e19590480dc141b0eefec9a5c51952aab4e97aedce8fdd`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/previous-original.md`: `da720e9599af7271686127b618b21038685e52a754031c2d43915c9d255f015f`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/previous-specification.md`: `1df6ae38c9f787c4d0994c676f149e0fc02ed94b85e5d6e0e65c7e236d744b3d`
- `docs/lean/statements/TR-13/reviews/source-refresh-2026-09-30/previous-statement.json`: `2db388f56748ad553da877334d097ecc01898f11e1523b3da857c03d5d0bdc7c`
- `tensor-computations/TR-13/README.md`: `fa34e46c5869e28c9f198a1aa78a4a5e026ba99dcbe67ce10d3410e426f7f70b`
