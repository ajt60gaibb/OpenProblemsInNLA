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

Final descriptive promotion changes only package metadata and display/status
text. Its final package receives a separate source-bound Linux receipt, to be
recorded here after that run and its independent original-artifact audit pass.
