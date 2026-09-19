# PF-03 supplementary final proof-body referee report

**Verdict: PASS for the reviewed proof bodies and recorded local-evidence correspondence. No blocking mathematical defect found.** This does not complete the publication gates or increase the verified-problem count.

Reviewer: `/root/recover_published_coverage`, an AI agent. I did not author, compile, repair, or edit the substantive proof implementations in this packet. I previously prepared PF-03's statements, transparent definitions, and literal-data translation. Consequently this report is an independent **proof-body** review but is **not independent of statement/definition authorship**. It must not count toward the two fully nonauthor final referees required by the coordinator. The definitions and target checks below are additional checks with that conflict disclosed.

## Exact reviewed inputs

The original sealed packet is `development/PF03-agent-packaging-v1/project` under `.local-recovery-20260918`, with author handoff SHA256 `b282175f2f9ad97cf324280013ee3c880477ca5bbaeb4b6a3dfdc112df57829c`. I verified all 74 handoff entries, then all 213 entries in the publication/local-evidence freeze SHA256 `dc090fe6ccba8a12f344cb2392267a8f8ffad3be5cf1b552bb821e40fb0099d1`. Every Lean source, frozen numerical plan and Comparator contract is unchanged in `publication/PF03/nonnegative-and-positive-factorizations/PF-03/lean`. The publication metadata changes record the observed local success and continue to mark final reviews and GitHub gates pending.

Key SHA256s:

| Input | SHA256 |
|---|---|
| `Solution.lean` | `bc6410c59b42efa2a0f0c605a8648e63f426be35546bdb1350a6f36268267917` |
| `NLA/PF03/Counterexample.lean` | `bff8769121f1ebac22c3591b4192f27a3df6220e6d5e7eefe9a2907bfea0b140` |
| `NLA/PF03/Definitions.lean` | `71bee5513dc9fd591dc35d4543471e29e54f95c146e52febd37396438ceccb98` |
| `Challenge.lean` | `63593ee0937a0ab2a9032646a38630b1a159e721902fc51929b84335110b2d55` |
| `comparator.json` | `2080ad692abd44a89cbb4f58864490ee42e543e1adeead31023540e1ee057c53` |
| `NUMERICAL_TARGETS.md` | `c81ccd2389dec24a94dce8701c086bad224ce82a3638ef1d8cb25199b1a398d7` |
| Holden manuscript | `0a4a17a034460f26a6e58a91bb1a47b6ef56ebc064a97b5d3fb9f7cf0e8a9064` |
| Actual local replay audit | `1656823e9c87a11fb434c20d167cc0635a38014940078795fc22fb98eab62137` |

The machine-readable manifests record all other exact source and guidance hashes. This approval covers those mathematical bytes, not arbitrary later edits.

## Original target and final logic

I read the retained canonical PF-03 entry and Holden's source manuscript at upstream revision `71563f17926cd826a892c2bba0e294894ee57a5c`, the 25 frozen Challenge contracts, numerical plan, all proof modules, and the final aggregation. Large literal files were inspected structurally and checked with a restricted independent rational-array parser rather than visually comparing hundreds of thousands of digits.

The implementation refutes the original universal rational boundary-factorability question. Factor width remains every positive finite integer; factors are entrywise nonnegative rational matrices and their Gram equality is exact. The final negation has no numerical-certificate, cone-description, injectivity, bounded-width, or unchecked geometric premise. `pf03_counterexample` discharges the internal cone and kernel premises before `canonical_negative_answer` negates the transparent universal assertion.

The witness uses a proved rational halfspace representation and appends five zero rows. This is a legitimate change of witness for the unchanged universal target. It does not verify the manuscript's explicit order-444 witness, strict positivity of all entries, or minimal real cp-rank claims; README, numerical plan and metadata explicitly exclude those extras. No solved-problem identity or mathematical authorship is reassigned.

## Substantive proof audit

1. **Seed, real embedding and irrational rays.** The cubic evaluation operations are proved using the actual positive real cube root of two. The independence of `1, alpha, alpha^2` is derived from the irreducible cubic/minimal polynomial, not stipulated. The rational-ray argument works for arbitrary real scaling, including zero, without dividing by an unproved nonzero scale. Its actual nonzero rational minor excludes nonzero rational points on each seed ray.

2. **Local positivity.** The generic three-dimensional quadratic lemma uses symmetry, an actual kernel vector with nonzero last coordinate, and two positive principal minors. Removing the kernel component and completing a two-dimensional square proves both nonnegativity and the entire kernel characterization. The seven `SeedLocalData` modules establish their literal arithmetic obligations; `SeedLocalAlgebra` transports the actual restrictions `C_i^T Q C_i` to these checked values. Symmetry justifies checking only the upper triangle.

3. **C09 actual generator bridge.** `TriangleRationalData` checks the actual derived generator matrix against the source literals. `TriangleCertificate` proves the barycentric coefficients positive, summing to one, and giving the actual alpha-vector under the actual triangle. These are the inputs later consumed to put the orthogonal seed columns in the full cone. The triangle and generator cache are not assumed to describe the desired geometry.

4. **C10 actual bilinear bridge.** All seven QG block modules check the complete 147-entry cubic product cache. The certificate then proves that evaluation of each cached pairing equals the actual real bilinear expression. The six cross-sign modules cover all 21 unordered cone pairs and all nine generator pairs for each, giving all 189 strict inequalities. Symmetry supplies reversed cone pairs. I independently parsed every source rational array, compared it to the primary JSON, and recomputed all 441 rational coefficients of QG; every equality passed. That Python check is supplementary evidence only.

5. **C12 full cone zero set.** Cone membership uses arbitrary real nonnegative coefficients on all 21 generators. The proof explicitly handles the all-zero coefficient family. Otherwise, expansion into local quadratic and cross-group terms gives nonnegative summands; a zero sum forces each summand to vanish. Strict cross-pairing positivity prevents two nonzero groups, and the local kernel result yields exactly a nonnegative seed ray. The reverse implication is also proved. No local-cone certificate is silently substituted for a statement about the full cone.

6. **Complete rational halfspace representation.** The Fourier–Motzkin step proves both directions using the zero-coefficient rows and every positive/negative cross row. Feasibility handles both-sided bounds, only one side, and no bounds. Induction eliminates any number of real coordinates while retaining rational coefficients. Encoding `x = V lambda` by two inequalities and `lambda >= 0` gives the whole cone, not an outer approximation or merely a list of supporting planes. Zero dimensions, empty row sets, and zero eliminated variables are covered by the generic proofs. Pointedness then gives real and rational kernel triviality, followed by a genuine rational linear left inverse through Mathlib.

7. **All factor widths.** `GramTransport` proves the necessary range identity from `CC^T = RR^T`, using zero sums of rational squares rather than assuming every column is already in the range of R. It establishes `RLC = C` and `(LC)(LC)^T = I` for arbitrary finite width. The actual whole-cone halfspace equality places every reduced nonnegative factor column in the cone. The finite trace identity and trace-zero quadratic form force every such column to be a rational quadratic zero and hence zero. This contradicts the identity Gram matrix. No rank/cp-rank bound restricts the candidate factor width. Generic transport and trace helpers also cover width zero, although the canonical factor definition requires positive width.

8. **Real symmetric frontier.** The topology is inherited on real symmetric matrices. `CPBoundary` proves nonnegative diagonal entries for every completely positive matrix, then subtracts a positive quantity from a zero diagonal entry along an explicitly symmetric continuous path. Points on this path outside the cone tend to the CP witness. This proves membership in both relevant closures and therefore the actual frontier. It neither uses a rational topology nor assumes the CP cone closed. The padded witness has a valid real nonnegative factor, an exactly zero diagonal, and order at least five.

## Computation, reuse and proof engineering

Only three fixed endpoint inequalities use LeanCert. The two cubic endpoint inequalities use 160-bit checked dyadic arithmetic at a single point; subsequent signs use exact cubic rational forms and the proven root enclosure. I inspected the pinned LeanCert `PointIneq` and `Verification` paths: the selected kernel mode constructs a certificate proof and has no native fallback. Source calls consume these inequalities through `CubicLowerBounds`, the local/triangle/cross certificates, the cone argument and final obstruction. This is source-level consumption analysis; an exported-proof-body Linux audit is still pending.

The proof avoids 54,264 facet computations and the expanded order-444 Gram matrix. Symmetry and QG reuse reduce repeated arithmetic, while the width, cone and boundary arguments are symbolic. The numerical work is divided into bounded modules. No interval-domain restriction weakens the target.

I performed a bounded search in the pinned Mathlib convex-cone and linear-algebra sources. `Geometry/Convex/Cone/DualFinite.lean` provides the `DualFG` language, but its contents do not provide the needed rational-coefficient projection bridge for real cone points. The explicit Fourier–Motzkin proof is justified for this project. Existing finite-sum, linear-left-inverse, matrix, continuity, algebraic-independence and minimal-polynomial APIs are reused. The general projection, Gram-transport and quadratic-kernel lemmas are separated from this seed. Repeated small arithmetic blocks serve bounded compilation and coverage rather than replacing mathematical reasoning.

## Observed evidence and limits

I did **not** execute Lean, Lake, Comparator, raw-kernel export, sandbox tests, or GitHub workflows. I inspected and independently hash-authenticated the existing local evidence: 30 lossless receipts, 60 module success records including Solution, their recorded log hashes, and 415 reuse links with source correspondence. The exact aggregate was actually executed by the coordinator in recovery-047, exit code zero, 4.668951792 seconds, with one compiler thread and `--memory=4096`. Its Solution source hash is listed above; its log SHA256 is `9957e173bcefb9aea19d374484af59a07648949ef065ea41b2d16baf2019923f` and output SHA256 is `fbafbc95c29044da637e33de83fe5f8d1e495c1e102e50d7cb77ffaa547e1bed`.

The observed aggregate log reports exactly the 25 frozen contract names, each with only `propext`, `Classical.choice`, and `Quot.sound`. The aggregate source requests all 25 kernel-trust assertions. A static import check finds 60 local modules including Solution, excludes Challenge, and finds no `sorry`, `admit`, custom `axiom`, `native_decide`, unsafe or externally implemented source declaration in that closure. Static inspection does not substitute for the recorded axiom audit or the still-required independent Linux checks. Reading authenticated records is not a new execution, and neither hashes nor this report establish an infallible trust guarantee.

The publication metadata accurately separates actual local success from pending final nonauthor reviews, GitHub Comparator and raw-kernel/sandbox/negative controls. A standalone `lake build Solution` is the documented project entrypoint but is not claimed as an executed local command. Historical frozen draft comments and initial environment snapshots are identified as historical. The 25 deliberate Challenge holes remain in the separate reference environment. The Comparator configuration has no replaceable definitions and permits only the three standard foundational axioms. I have not run Comparator and make no claim that it passed.

Sidney Holden retains original mathematics and exact data credit; George Stepaniants receives formalization credit with Department of Computing and Mathematical Sciences, California Institute of Technology. Substantial AI assistance is disclosed; no human peer review or author endorsement is claimed. No contact email was added by this review.

I applied the repository review guidance at upstream `71563f17926cd826a892c2bba0e294894ee57a5c` and the locally preserved Tau Ceti revision `afb424eda89e8ac96d9eb69f6a88972055a4cd1b` rubrics for correctness, proof quality, generality, reuse and attribution. This is an AI review under adapted guidance, not an official Tau Ceti service run.

## Disposition

No code changes are requested by this proof-body review. Continue the two fully nonauthor final reviews and the actual exact-published-source Linux gates before canonical Lean promotion. My earlier statement/definition authorship excludes this report from the strict two-referee count. Metadata may later record completed checks using their real evidence; changes to the reviewed mathematical bytes require a corresponding review update. The completed-target count remains unchanged by this report.
