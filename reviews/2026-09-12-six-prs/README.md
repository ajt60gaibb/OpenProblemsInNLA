# Independent audits of PRs 160, 162, 164, 165, 166 and 167

**Verdict: all six submissions pass mathematical and publication review.** The combined integration is subject to successful required CI and actual Linux verification before merge. This record distinguishes the independent source audits and authenticated earlier runs from that final acceptance gate.

Reviewed published base: `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. Combined contribution tree: `ed179ae3b431a861852508243cb5b37a256c4b0f`. Audit date: 12 September 2026. Reviews were performed by the coordinating Codex AI agent and three independent delegated Codex agents, separately from the submission authors and their recorded reviews. These audits are not external human peer review.

| PR | Entry | Decision | Independent evidence |
| --- | --- | --- | --- |
| [160](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/160) | MI-29 | Lean verified | [Full audit](pr160.md) |
| [162](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/162) | TR-07 | Solved, complete affirmative answer | [Full proof audit](pr162.md) |
| [164](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/164) | TR-03 | Partially resolved, one-column identity | [Full special-case audit](pr164.md) |
| [165](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/165) | MI-21 | Lean verified | [Full audit](pr165.md) |
| [166](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/166) | MI-07 | Lean verified | [Full audit](pr166-pr167.md), [second review](mi06-mi07-second-review.md) |
| [167](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/167) | MI-06 | Lean verified | [Full audit](pr166-pr167.md), [second review](mi06-mi07-second-review.md) |

All four formalizations preserve their full original universal targets and prove counterexamples with actual functional-calculus operations and ordinary matrix order or the actual specified norm. The audits reconstruct their exact witnesses independently, authenticate current upstream Linux artifacts and source receipts, and review default-kernel acceptance, transitive axiom reports, pinned dependencies and executed rejection controls. No local Linux rerun is claimed by the auditors. Current proof-run artifact ZIPs and checks are retained here; historical submission evidence remains in the unchanged projects.

TR-07's complete proof covers arbitrary deterministic signed columns, repeated values and unrestricted support intersections at fixed sparsity and finite aspect ratio. TR-03 proves the full k=1 slice and leaves the general k range unresolved. Mathematical credit and the distinction between informal and formal verification remain as submitted. Every changed publication PDF was rendered and inspected completely; the two new mathematical manuscripts and their problem TeX files were also compiled independently and compared with the committed PDFs.

## Integration preservation

The [independent integration review](integration-review.md) and [tree comparisons](integration-preservation-checks.json) show that all six full canonical problem directories and both Holden reference directories are byte-identical, including file modes, to their respective reviewed PR heads. All six heads remain ancestors of the integration branch. All other prior main files are unchanged except the five intended shared index/archive paths. The two archive conflicts preserve both new adjacent contributions; all preexisting archive prose and every new submission paragraph survive.

All 217 permanent IDs and canonical paths remain unchanged. The original mathematical targets remain on their canonical pages. All 13 generated indexes reproduce exactly. Counts are **10 Lean verified, 80 Solved, 56 Open and 71 Partially resolved**, hence **127 open targets**. The source changes need no mathematical correction; only shared index counts and adjacent resolution entries required reconciliation.

Local validation passed the mandatory ID validation, index generation and all 17 safeguard tests, all 68 repository tests with one Pandoc-dependent class skipped, all 12 harness tests, and the global math formatter. CI separately supplies the required Pandoc/rendering checks. The proof selector against the published base selects exactly MI-06, MI-07, MI-21 and MI-29.

The initial new-branch push run selected all existing formalizations because its before-revision was zero. Its MI-29 job failed while downloading Elan with curl error 35, connection reset by peer, before building or checking a proof. This transient setup failure is retained in `first-integration-failed-job.log`; it is not counted as successful verification. Acceptance requires a successful subsequent run on the complete final PR tree, with source identities rechecked.

## Three issues

- [161](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/161) is addressed by the complete TR-07 result in PR162; close after acceptance.
- [163](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/163) is addressed by the TR-03 partial result in PR164; close after acceptance while retaining Partially resolved status.
- [150](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/150) already has the requested clarification merged in PR151 and a substantive owner reply. The [independent issue audit](issue150.md) confirms it can be closed as completed; TR-08 remains Open.

Evidence files record the original isolated scratch paths used during review. The numerical checks are supporting diagnostics; the mathematical conclusions rest on the independently reconstructed arguments. This directory preserves reports, scripts, exact outputs, compile logs and downloaded proof receipts. Scratch page-render PNGs and rebuilt duplicate PDFs are omitted; visual review results are documented in each report.
