# Maintainer review of Lean promotions, 12 September 2026

**Verdict: accept the complete negative resolutions of IE-19, MI-19 and IE-18 as Lean verified.** This audit reviewed the actual Lean definitions, proofs and original problem statements, independently reconstructed the exact arithmetic, and authenticated the current upstream Linux verification evidence. The review was performed by Codex AI agents; it is not external human peer review.

| PR | Problem | Independent source/fidelity review | Current upstream kernel run |
| --- | --- | --- | --- |
| [154](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/154) | IE-19 | [Review](PR154-IE-19.md) | [34706410632](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/34706410632) |
| [155](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/155) | MI-19 | [Review](PR155-MI-19.md) | [34706412117](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/34706412117) |
| [156](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/156) | IE-18 | [Review](PR156-IE-18.md) | [34706412720](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/34706412720) |

## Mechanical evidence and source identity

The coordinating reviewer downloaded these runs from the upstream repository. GitHub's commit API confirms that each recorded verification revision has the published base `02b807770fca860ef810cc048d6849224b8f93e1` and the exact corresponding reviewed PR head as parents. All 196, 146 and 91 project input hashes, respectively, match both those PRs and the combined integration tree. The [evidence summary](upstream-evidence.json) records the reviewed heads, merge revisions, selected declarations and artifact digests.

The actual Comparator logs record fresh proof elaboration, exact Challenge/Solution checks without definition holes, the axiom allowlist `propext`, `Classical.choice`, `Quot.sound`, and successful Lean default-kernel replay. Sandbox controls, invalid-proof and statement-mismatch controls, and rejection of sorry/native-trust axioms all passed. Although the separate checker-controls job is skipped when shared tooling is unchanged, every project verification runs those controls before building its proof. These PRs do not change the shared verifier, source lock or workflow. The deliberately incomplete Challenge modules are isolated from the proved Solution imports.

This audit **reviewed remote Linux execution**; it did not claim a local Lean or Linux-sandbox rerun. Independent statement correspondence is supplied by the source reviews, separately from mechanical acceptance.

## Integration and scope

The three entire canonical problem directories, including proof sources, manifests, archived evidence, README, TeX and PDF, are retained from their reviewed heads. Integration reconciles the adjacent resolution entries and regenerates the shared indexes; all 217 permanent IDs and canonical paths remain unchanged. The resulting counts are 5 Lean verified, 84 Solved, 57 Open and 71 Partially resolved. All 77 repository tests and 12 harness tests passed locally after installing the declared metadata dependencies; the GitHub math check passed. All eight updated PDF pages were rendered and visually inspected.

The formal status applies to each original conjecture's complete negative answer. It does not promote the additional IE-19 sharp-infimum theorem, MI-19 perturbation/all-q extensions, or IE-18 parameter-family/asymptotic questions to formally verified results. Mathematical counterexample credit remains with Matthew J. Colbrook; Lean formalization credit remains with George Stepaniants. The original evidence archives remain unchanged.

## Subsequent RA-03 audit

The separate [PR #157 audit](PR157/README.md) reviews the later RA-03 promotion against the main branch containing the three promotions above. It preserves their evidence and records the resulting six Lean-verified entries.

## Subsequent MI-26 audit

The [PR #169 audit](PR169/README.md) records independent review and authenticated kernel evidence for the later MI-26 promotion, integrated after the six contributions in PR #168.
