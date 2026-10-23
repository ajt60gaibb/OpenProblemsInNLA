# TR-14 actual block images, partitions and ordinary lower source review

Reviewer: `/root`, OpenAI Codex AI agent; date 2026-10-18.
Verdict: **approve the named other-author sources**.

I read the five complete frozen modules below and their actual helper definitions.
None was authored by this reviewer. My own corner, iteration and numerical
arithmetic modules are prerequisites and are excluded from independent source
approval here; their separate independent reviews are retained.

| Module | SHA-256 |
| --- | --- |
| CyclicSpanDimension | `c430e82a28d5c738da7aa969c193008e7a7a223270d9845470809cfb1415f009` |
| BlockPolynomialImage | `13ad26f8cbdc29ed19f398335c9db90a7783a6f9019363e39413c7405b463b6a` |
| LocalBlockSupport | `34abf64031ed15a4abf5a53459f3480d2a598272d716a5d9af0e39e3f05b2883` |
| OrthogonalBlockDimensions | `0b231b3e62eb86071bc5cdd16dd2f08fe4a95f180aa6853717b26792a8485264` |
| NormalizedOrdinaryLower | `ff0063cde64968718d5456b96152157480d2a17038ba4de0676a0d4b22f5db48` |

The cyclic dimension proof establishes the real saturation condition: membership
of the next orbit vector makes the prefix invariant and forces it to contain the
entire orbit. Before saturation, adjoining the next vector raises dimension by
one. This proves the exact min(n,actual full orbit dimension) formula, including
n=0 and x=0, without a supplied minimal-polynomial or rank statement.

The quotient specialization identifies the actual full orbit with the actual
multiplication image by expanding every quotient element in the monic power
basis. The finite coefficient map has exactly the actual prefix span as its
range. The calculated dimension is therefore for the required actual space.

The local residue is the actual zero coefficient in each positive-multiplicity
truncated factor. Nilpotence of the residue-zero ideal and idempotence force each
whole local component to be zero or one. A nonzero quotient idempotent has nonempty
actual root support, and orthogonal nonzero idempotents cannot share a supported
whole factor. The support count includes repeated roots without splitting their
derivative coordinates.

The orthogonal block equivalence is the actual map x↦(e_j*x), with inverse sum.
Both inverse identities use the actual sum-one and orthogonality equations; it
works with zero components. Projecting the actual primitive indicators to either
ambient factor therefore gives the required exact dimension partition.

The full normalized lower starts from any supplied ordinary width, takes an
actual least width R≤w, proves independence of its actual rank-one functions,
and constructs genuine separate graph units for the same fixed quotient chart.
The actual normalized functional is Frobenius on the first factor, annihilates
the actual product, has nonzero scalar-coordinate coefficients, and the scalar
projection is onto. The actual stabilizer is reduced. Its primitive equivalence
constructs nonzero indicators; scalar surjectivity excludes a zero first
component. Actual whole-factor support and exact dimension partitions, with the
proved actual mode image ranks and intrinsic block inequality, discharge every
numerical lower premise. The resulting exact minimum bound holds for R and hence
for every supplied w. The general-n wrapper only converts n=q+1; it adds no
mathematical assumption or dimension restriction.

This report is an independent source/math review. The root-authored Final
consuming these results compiled with LeanCert kernel assertions and only the
standard three axioms; that was a development compilation with campaign objects,
not a new fresh-closure audit. Independent fresh immutable source/kernel evidence
is retained in NORMALIZED_ORDINARY_LOWER_REVIEW_2_2026-10-18.md,
PRIMITIVE_BLOCK_DIMENSIONS_INDEPENDENT_REVIEW_3_2026-10-18.md and
BLOCK_SUPPORT_AND_PARTITIONS_INDEPENDENT_REVIEW_3_2026-10-18.md. The separate full
shared/canonical closure audits inspect theorem kinds, private constants and the
literal unchanged Target. Actual isolated Linux Comparator verification is a
further gate. No external human peer review or catalog promotion is claimed.
