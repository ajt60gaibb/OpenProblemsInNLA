# IE-04 source and actual development-build reconciliation

**Verdict: ACCEPT the complete reviewed source and its actual successful Linux development build. Canonical verification remains pending.** This is an addendum to my independent complete mathematical source review, [REVIEW.md](../REVIEW.md), SHA256 `cdd334884bbf0b2d653ef7be37f290d5f7df170ae6c1045b6dcb2eef1ebbb7b1`. No mathematical source changes or corrections are requested.

Reviewer: `/root/next_inequalities`, independent non-implementing Codex AI agent, 15 September 2026. I inspected the actual command logs, raw GitHub job transcript, archive contents, metadata, receipt, source Git objects and previous approved inputs. I did not invoke Lean or Lake locally, change any proof, rerun CI, or use the root audit's conclusion as a substitute for these checks.

## Source and runtime identity

Run [35031607095](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35031607095) checked Git commit `4bd2d76ec6e37696ff0c2d5feacf21e342371f27` on an Ubuntu Linux runner, UID 1001, Lean 4.33.1. The job is `104591152756`; artifact `10421054240` has SHA256 `592e5315a1d4af6b012ee7216a5214a128c4f21aceecec27614b9aba2e6c27a9`. The downloaded ZIP digest matches the GitHub artifact metadata, fetch identity and actual uploader line in the raw job log. Every extracted archive member matches the ZIP bytes.

I independently matched **all 115** initial shared source hashes to actual Git blobs under `.lean-development/`. All nine recorded commands retain exactly those same source hashes afterward, and all nine command-log hashes match the receipt. Every command log also occurs byte-for-byte in the raw job transcript after removal of GitHub's timestamp prefixes. The raw checkout identifies the same commit. All ten actual dependency revisions equal the pinned manifest, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

For IE-04, all 27 previously approved package files still match the author tree. Every file in its complete 14-module implementation graph, the independent Challenge and numerical-target file matches the accepted Git/receipt input. The root `Solution.lean` is copied into the shared development namespace without byte changes; Challenge is copied into `Challenges/` likewise. The frozen definitions, public signatures and numerical statements remain unchanged. No unreviewed mathematical edit has entered the accepted graph.

`AUDIT.json` records the complete source mapping and all target axiom lines. Its SHA256 is `5e146730095577a7c7c49b14048378b495361e412875962de73c1e056eeff2a2`. `INPUTS.json` binds the retained runtime evidence and exact runtime driver/workflow sources. The independent audit script is retained alongside them; it runs only Python and read-only Git commands.

## Actual complete-project result

| Actual log | Command exit | SHA256 |
| --- | --- | --- |
| `IE-04-modules.log` | `0` | `31aa8460de1a3373925b7700855ba654204964ece902e016cac2df036954f26a` |
| `IE-04-challenge.log` | `0` | `e39ba6a375d018fd4217bfde0b879c3a3990a27bbaae360d003c51ce5c73d42b` |

I read the full IE-04 proof and Challenge logs. The proof command is `lake build NLA.IE04.Solution`, exits zero, explicitly builds all 14 graph modules and concludes `Build completed successfully`. Each of the 21 requested targets has an actual Solution axiom report, and every report lists only `propext`, `Classical.choice`, and `Quot.sound`. All requested LeanCert kernel assertions therefore pass on this source graph. The accepted proof log contains no error, `sorryAx`, native dependency, unrecognized axiom, or declaration hole. The independent Challenge command exits zero with exactly 21 expected placeholder warnings; those warnings establish declaration elaboration only.

The accepted IE-04 Robustness, GaussianBox and ProbabilityTail bytes are exactly the repairs reviewed in the prior report. The entire actual GEPP/strict-pivot/nonsingularity bridge, Gaussian product law, measurable event, all-real asymptotic argument and final negation now compile together. All 21 Solution trust assertions and their transitive axiom reports are accepted. The fixed LeanCert exp(-2)>1/8 certificate is actually consumed by the density, interval, product probability and final tail proofs.

The overall workflow's red status is retained honestly: the later, separate MF-12 module command failed. The receipt has precisely that one failed command. Both complete IE-04 commands passed before it, their graph is independent of MF-12, and no such errors occur in the accepted IE-04 log. This report does not change the aggregate run's result to success.

## Remaining gates and scope

This development driver checks the complete imports and requested theorem dependencies but does **not** run the canonical sandboxed Comparator, independent default-kernel replay, or mandatory negative controls. Its receipt explicitly has `comparator_run: false` and `mathematical_verification: false`. I preserve those distinctions: development acceptance is not final whole-problem verification, a publication approval, or a count increment.

The canonical package must still be checked with the repository's full protocol on source-matched bytes, followed by two independent final source/runtime addenda. The original mathematical attribution, George Stepaniants's formalization credit and Caltech department affiliation, and the earlier full mathematical scope assessment remain unchanged. Any packaging contribution I subsequently make is separate from this independent mathematical-source and development-evidence review; another reviewer must inspect such packaging changes.
