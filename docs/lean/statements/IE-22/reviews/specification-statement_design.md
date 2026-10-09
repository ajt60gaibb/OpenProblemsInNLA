# IE-22: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for the bound specification bytes.

## Fidelity reasoning

1. The full target retains the deterministic supremum over every real unit-row matrix, with no random distribution, genericity or independence hypothesis. Row subset size is exactly floor(theta*m), with real multiplication first.

2. The sSq infimum is over complete finite row subsets and all Euclidean unit vectors; nonnegative continuity and compactness justify equality to s_theta squared. Zero retained rows and rank-deficient maps remain zero, not a least-positive singular value.

3. The matrix supremum is over a nonempty bounded set in positive dimensions: repeated coordinate rows witness nonemptiness, and Cauchy-Schwarz bounds sSq by k<=m. Thus real sSup has its intended finite meaning. The square roots preserve the source placement sqrt(n/m)*s_theta.

4. The quantile is exact under the standard Gaussian, with positive a and h given by the normalized Gaussian second-moment integral. The proposed constant is its nonnegative square root; no independent h or quantile oracle occurs.

5. Upper puts all positive epsilon first, then dimension/aspect thresholds N,R before every positive n,m. R*n<=m is exactly m/n>=R when n>0. Natural thresholds preserve existential integer-threshold eventuality by enlarging any negative original threshold.

6. The second conjunct quantifies every smaller real c and negates that same complete Upper property. This includes negative candidates and exactly preserves the source optimality quantifiers; it does not replace them by one witness sequence or require violations for every tolerance.

7. The original manuscript Theorem 2 and Sections 6-7 support the credited resolution, but their stronger all-m upper bound and explicit rate are not silently added to the original proposition.

8. The old SupremumConverges definition was inspected and indeed omits n->infinity. The stated n=1 counterexample is valid: sSq=floor(theta*m) and the normalized limit is sqrt(theta)>sqrt(h_theta). Excluding that erroneous extension preserves the canonical target rather than weakening it.

9. Full canonical README and ORIGINAL agree byte-for-byte. The specification, original source, credited manuscript and old definition source are bound below; this review precedes any new implementation.

## Bound inputs

- docs/lean/statements/IE-22/NUMERICAL_TARGETS.md: f42039df583dc45692c44053fbb69dcf713c04296be55a2b3b3972b2a7a92ece
- docs/lean/statements/IE-22/ORIGINAL.md: 273ce377e8de3f575be53104f156f0436ffb571a3a464bb5d5693c0aa510c344
- linear-systems-and-elimination/IE-22/README.md: 273ce377e8de3f575be53104f156f0436ffb571a3a464bb5d5693c0aa510c344
- linear-systems-and-elimination/IE-22/lean/Definitions.lean: eea214cb498a2ac48c3aad5afefd9489a0eb87fd2e92dd1059db51ef4332240b
- references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex: 31a1949c07f63408538f04e3803d90e8d3d0c3d1e47dc89a2ffa5a04ef4f3880
- references/colbrook-recovered-2026-09-11/verification/reviews/IE-21-22-review.md: d174419a6f71de369b7608a53b36dffa9cd815e3fd65a70d16457318cb68234d

## Limits

Independent AI-agent preimplementation mathematical/model specification review, independent of /root/infra_audit, its author. No final Lean API use, compilation, target theorem or numerical certificate is approved by this report. Final source/import/pin review remains required.
