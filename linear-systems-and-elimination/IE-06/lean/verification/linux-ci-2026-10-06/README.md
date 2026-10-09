# IE-06 authoritative Linux verification — 6 October 2026

**Passed:** the full pinned Comparator accepted the actual six IE-06 exports
after building and exporting the independent Challenge and Solution modules
and replaying the exported solution through Lean's default kernel. The strict
Linux isolation probes and all rejection controls also passed. This is the
completed authoritative route, separate from the earlier local library check.

## Provenance and immutable receipt

- [Workflow run 37513136002](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/37513136002),
  [IE-06 verification job 112439363988](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/37513136002/job/112439363988).
- PR head: `05b1c83e11042d7067cd51c5a4bfc0265e7390f4`.
- Tested pull-request merge commit, as recorded by the harness:
  `6091e87aa8538ea31df21fd06cce3d9e42f65c2a`.
- Artifact: `lean-IE-06`, ID `11436961581`, created `2026-10-06T18:55:01Z`.
- Original [result.json](verify-20261006T184228Z-4239/result.json) SHA-256:
  `e8d6ccc4501c435ca30d48bb8b9940ce6bcba9417b884b9625f4414ef102f168`.
- Original result: `comparator-accepted`. The command's semantic-review field
  remains `not-performed-by-this-command`.

All 13 files in the downloaded small CI artifact are retained byte-for-byte,
including bootstrap logs. [artifact-files.json](artifact-files.json) records
their hashes and sizes. [provenance.json](provenance.json) records the original
GitHub artifact metadata and its reported archive digest. The GitHub artifact
may expire; these retained files preserve the evidence. The source lock copied
here has SHA-256
`b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, matching
the original receipt. No original receipt or log has been edited.

## Exact checked targets and trust boundary

The receipt's configuration selects these six declarations, each exactly once:

1. `NLA.IE06.squareRootUpperBound`
2. `NLA.IE06.schurSubpolynomialTail`
3. `NLA.IE06.gaussianMatrix_probability`
4. `NLA.IE06.exceedanceEvent_measurable`
5. `NLA.IE06.admissiblePath_exists`
6. `NLA.IE06.gaussianMatrix_singular_null`

`definition_names` is empty: no replaceable definition holes are permitted.
The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The frozen Challenge has six deliberate reference placeholders; the candidate
Solution does not import them. All six Solution exports print only the three
permitted foundational axioms in the retained build log.

The receipt pins Lean 4.33.1 on Linux x86-64, the Forsythe checker source
revision `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, the full
[source lock](source-lock.json), and hashes of the actual Comparator,
`lean4export`, and Landrun executables. The run uses the repository's unchanged
shared harness and dependency pins. Mathlib cache acquisition is recorded;
the actual exported solution is subsequently replayed through Lean's kernel.
This is a fresh exported-declaration replay within Comparator, not a second
proof-assistant implementation or a claim of human mathematical review.

## What the logs establish

| Check | Retained evidence |
| --- | --- |
| Fresh actual proof comparison and exporter | [comparator.log](verify-20261006T184228Z-4239/comparator.log) builds Challenge and Solution, exports the six named targets from both, accepts the solution through Lean's default kernel, reports `Your solution is okay!`, and exits 0. |
| Actual non-root Linux sandbox | [sandbox.log](verify-20261006T184228Z-4239/sandbox.log) runs as UID 1001. Build writes are limited to the designated `.lake`; export writes are denied. Namespace, host-process, host-network, AF_UNIX, capability, and unsupported-option controls pass. |
| Raw-kernel replay controls | [kernel-controls.log](verify-20261006T184228Z-4239/kernel-controls.log) accepts the honest inductive/quotient fixture, rejects the invalid raw proof, and rejects the quotient post-check mismatch. All three cases pass. |
| Comparator regressions | [comparator-controls.log](verify-20261006T184228Z-4239/comparator-controls.log) passes all five expected match/mismatch/axiom cases. |
| Admitted-proof rejection | [negative-sorry.log](verify-20261006T184228Z-4239/negative-sorry.log) rejects `sorryAx` and exits 1 as required. |
| Native-proof rejection | [negative-native.log](verify-20261006T184228Z-4239/negative-native.log) rejects the generated native-decide axiom and exits 1 as required. |
| Dependencies and bootstrap | [dependencies.log](verify-20261006T184228Z-4239/dependencies.log), [mathlib-cache.log](verify-20261006T184228Z-4239/mathlib-cache.log), and [bootstrap logs](bootstrap/) retain the setup evidence. |

The Linux run checks the selected six targets and their exported dependency
closure. The earlier local receipt separately records the exhaustive audit of
3,229 owned declarations in 113 concrete modules. Those scopes are not conflated.
Independent AI-agent mathematical reviews remain under `../../reviews/`; the
CI command does not certify the correspondence to the manuscript by itself.

## Source identity and the later status promotion

Before any status-document edit, all **1,139** package-input hashes in the CI
receipt matched the promotion checkout at
`6ea93e3194bed8b2e65b846573ddafbfd6b66eff`.
[input-identity-before-promotion.json](input-identity-before-promotion.json)
records that comparison. The complete hash map remains in the original result.

The subsequent status promotion updates six current-facing package documents
and adds this evidence directory. [promotion-document-changes.json](promotion-document-changes.json)
records those documentation deltas against the tested snapshot. Lean proof
sources, `comparator.json`, toolchain/dependency pins, frozen review/source
snapshots, and historical receipts remain unchanged. The existing delivery
manifest is preserved as an inventory of its historical publication snapshot;
it does not purport to include this later evidence or these status edits.
No new proof result, manuscript-author endorsement, or human peer review is
claimed by the documentation promotion.
