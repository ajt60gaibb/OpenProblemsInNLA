# TR-04 actual Linux Comparator and kernel receipt

The complete candidate proof was accepted by
[run 40405628070](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40405628070),
[job 121862750146](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40405628070/job/121862750146),
on [draft PR 370](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/370).
This was a pull-request merge execution, with exact checked-out merge
`d9d0a8f163c2c0309e349cfbe839d53bece11643` and parents
`01141f415715a27473cabc1f35ef898e86aafae2` (base) and
`027aaefbadf602ac460d0cf4cae7beed3181d712` (proof candidate).

The [original GitHub artifact 12691512992](campaign-2026-10-26/linux-pr370-candidate/original-GitHub-artifact12691512992.zip)
is 33,291 bytes, SHA-256
`10ac3d685a1a7d7e4048857fe34d92908ecd8fa2308aa887ac1eb58c5d3dcbf3`.
The [original decoded UTF-8 raw job](campaign-2026-10-26/linux-pr370-candidate/job121862750146.log)
is 244,896 bytes, SHA-256
`a55c444320b28ce446a05b7fe78c3a3033d5e9f1495814e9b6eec9ac90c97e5b`.
The ZIP is retained unchanged; a deterministic gzip copy preserves the raw log
bytes. Original API values, connector responses and collection details are
retained in the [collection provenance](campaign-2026-10-26/linux-pr370-candidate/COLLECTION_PROVENANCE.json).

The [independent actual-evidence approval](campaign-2026-10-26/independent-linux-candidate-algebra/APPROVAL.json)
and [795-check report](campaign-2026-10-26/independent-linux-candidate-algebra/terminal-result.json)
bind all 205 canonical inputs, all 184 copied sources, all ten dependency
revisions, all 25 original live/archive pairs, the exact merge parents,
original ZIP/upload digest, raw command segments, and all 217 permanent IDs.
The read-only auditor records what the Linux job actually compiled: 187
imported project modules, including all 179 proof modules. `Check`, `Identity`,
and the reviewed mirror are input-bound there and separately compiled in both
190-source local audits.

Comparator compared `FullChallenge` and `FullSolution` at exactly
`candidate_count_le_first_mode`, `cyclic_window_count_le_first_mode`, and
`NLA.TR04.target`, with no definition holes. Both count proofs have empty
transitive axiom sets; the complete Target uses exactly `propext`,
`Classical.choice`, and `Quot.sound`. The default kernel accepted the exported
solution; the generated LeanCert consumer checked that each selected constant
is a theorem and passes `#assert_trust kernel`.

The same original job also passed raw-kernel mismatch controls, five actual
Comparator regressions, `sorryAx` and `native_decide` rejections, both sandbox
modes, and the write/network/namespace/AF_UNIX isolation controls. The
[mathematical source review](campaign-2026-10-26/independent-full-target-review/ACCEPTANCE.json)
is separately bound; the harness does not perform that review.

## Final promoted package

The independently approved descriptive promotion at commit
`09cd782576559502787fb536bc1427bf64b7b3e4` passed
[final run 40408919808](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40408919808),
[job 121875088207](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40408919808/job/121875088207).
Its actual executed PR merge is `5c58fa518732636edcb21c377f8014fa00f34480`,
with exact parents `01141f415715a27473cabc1f35ef898e86aafae2` and
`09cd782576559502787fb536bc1427bf64b7b3e4`.

The [unchanged original final ZIP](campaign-2026-10-26/linux-pr370-promotion/original-GitHub-artifact12692842329.zip)
(artifact 12692842329) is 33,585 bytes, SHA-256
`bd48f52a1f448b3f09b8f39e2a07a946b38bc9e610d9ca55f965a9a80196efcc`.
The [original final raw job](campaign-2026-10-26/linux-pr370-promotion/job121875088207.log)
is 248,078 bytes, SHA-256
`03be81cfc841504b92aa8a41e47d2798ba97996d9a18962779bb5b94f884f920`.
The [root collection provenance](campaign-2026-10-26/linux-pr370-promotion/COLLECTION_PROVENANCE.json)
retains the original API values and exact byte identities.

Two independent final audits pass: [827 checks](campaign-2026-10-26/independent-linux-promotion-algebra/APPROVAL.json)
and [1,214 checks with a separately fetched original ZIP/raw/API collection](campaign-2026-10-26/independent-linux-promotion-review/terminal-result.json).
Both verify every final canonical input, the exact merge parents, all selected
exports and their transitive axioms, actual default-kernel and LeanCert kernel
acceptance, and every rejection/isolation/raw-command control. All 190 Lean
inputs and 184 shared-source copies are identical to the accepted proof
candidate. Of the 205 canonical inputs, only `formalization.yaml` changed.
The actual final Linux import build again contains 187 project modules,
including all 179 proof modules.

The [post-promotion display audit](campaign-2026-10-26/independent-linux-promotion-review/POSTPROMOTION_DISPLAY.json)
checks all 217 IDs, 216 unchanged other problem pages, the exact approved README
replacement and original statement suffix, 13 reproduced catalog outputs,
and all 17 numbering tests. The branch has 87 Lean verified and 31 Solved
entries. The [historical checkpoint audit](campaign-2026-10-26/independent-linux-promotion-review/HISTORICAL_CHECKPOINT.json)
binds the earlier 6,349-artifact source index to checkpoint
`e7b6c9c592d823973aac5d39a6dbe6c81c0005ce`, where the original README and
pre-promotion metadata remain live byte for byte. Historical checks should be
replayed at that checkpoint; final package checks use the promoted 205-input
freeze and this final run.
