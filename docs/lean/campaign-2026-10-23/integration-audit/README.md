# Newly discovered complete-proof branches, 23 October 2026

Independent existing-evidence audit by OpenAI Codex AI agent `/root/inventory`.
**SP-12, TR-14 and PF-05 already have complete unchanged Target proofs, retained
independent full-source reviews, and actual promoted-package Linux Comparator
and LeanCert kernel receipts. Reuse and integrate these proofs; do not implement
them again. TR-06 remains incomplete.**

This report does not execute Lean, Linux CI or the strict artifact replay tool,
and does not claim a new independent review of every mathematical prerequisite.
It independently binds the existing reviewed proof wrappers, exact statements,
current package sources, original artifacts and live GitHub jobs/artifact
digests. The standalone audit passed all checks.

## Published main and integration checkpoint

Published main remains `5487945e5a72abd952b0c89915915de8cc9b3e65`: **80 Lean
verified, 38 Solved**. The earlier fixed published inventory remains accurate
for that immutable commit; it missed these later stacked branches.

The inspected integration checkpoint is
`42d1665800d0185581149ef494e03055b533d636`: **83 Lean verified, 35 Solved**.
It includes all three promoted full proofs and their final receipts, before the
incomplete TR-06 recovery. All 217 registered ID/path pairs equal published
main. Each package's live statement and frozen Reviewed statement equal their
published-main counterparts byte for byte; its archived ORIGINAL equals the
published canonical README and its specification is unchanged. Retained
promotion reviews separately address notice/status/date and TeX/PDF changes.

## Exact fetched branch heads and PR state

| Branch | Fetched head | Actual state |
| --- | --- | --- |
| `codex/sp12-kernel-proof-oct18` | `d250bd50d602ec7fd6e55bb4fd19494c5e19b045` | [PR #362](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/362) is closed and merged into `codex/solved-lean-campaign-oct17`; complete proof and promoted-package receipt. |
| `codex/tr14-complete-proof-oct18` | `d6b233b488c168da5496fa9cbd14929e79fa788e` | [PR #363](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/363), reviewed head `4071ed5e`, is closed and merged into the campaign branch. The fetched branch subsequently received PF-05's merged PR #364. |
| `codex/pf05-complete-proof-oct18` | `c4c7be592c51c8ba81d1579082813310a22b356d` | [PR #364](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/364) is closed and merged into the TR-14 branch. Its old description saying promoted-package CI is pending is superseded by recovered actual receipts in `42d16658`. |
| `codex/tr06-complete-proof-oct23` | `fa48059568762742b07f124c0e6ff65ef2ca212d` | No PR found in the exact-head search. The branch explicitly retains an incomplete support checkpoint; its name is not a proof-completion claim. |

The three merged PRs were stacked on campaign branches, so they did not change
published main. The integration checkpoint contains the exact current packages
from all three heads; this audit verified every package input byte against both
the branch and the authoritative checked commit.

## Full-target and current-package evidence

| ID | Exact exported result and existing source review | Latest verified promoted package |
| --- | --- | --- |
| SP-12 | `NLA.SP12.target : NLA.Statements.SP12.Target`: exact real symmetric graph pattern, nonnegative quadratic form, full SAP and nullity at least actual chromatic number minus one, for every positive finite graph. Canonical independent review binds Solution SHA `d09d569d…`; 55 actual Lean inputs, 56 fresh source commands, 379 declaration/270 theorem-kind checks. | [Run 39149417211](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39149417211), [job 117739903353](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39149417211/job/117739903353), checked `a7adfc8e30ad284f42ec2ea0221a990ee9804031`; artifact `12143944681`, ZIP SHA `b0727fbe155790ef58328831a7630e121b8450c3fd91daaaf662fd4b7a20841f`. Existing independent strict replay: 40 passing controls, all 96 inputs. |
| TR-14 | `NLA.TR14.target : NLA.Statements.TR14.Target`: ordinary/symmetric width equivalence for all `m≥3`, `n≥2`, complex Hankel data and natural widths, including zero and exceptional cases. Existing full review binds Final SHA `31ecd9e9…`; both symmetric constructions and unrestricted ordinary lower bound are now proved. Canonical audit: 82 Lean inputs, 83 commands, 453 declaration/355 theorem-kind checks. | [Run 39174291223](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39174291223), [job 117814377068](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39174291223/job/117814377068), checked `16a1150d81f606ed6a8333be8c04730e0a477525`; artifact `12154172015`, ZIP SHA `2bcae45d596895e34b712c667737bdd263de3950c7654a030fe1b1e292ee340d`. Existing independent strict replay: 41 passing controls, all 139 inputs. |
| PF-05 | `NLA.PF05.target : NLA.Statements.PF05.Target`: full actual straight-line infinitesimal rigidity/uniqueness equivalence, arbitrary rank-three PSD-rank-two matrices and fixed factors, all zero patterns, singular factors and repeated rays. Canonical review binds Solution SHA `59265ce1…`; all 46 actual Lean inputs, 47 source commands, 384 declaration/299 theorem-kind checks. | [Run 39176870923](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39176870923), [job 117821318204](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39176870923/job/117821318204), checked `c4c7be592c51c8ba81d1579082813310a22b356d`; artifact `12154394713`, ZIP SHA `b0a0fa9da8219b6517192134e59475746550209557f0c719ca6027bd74386c03`. Two recovered strict replays: 41 passing controls and all 90 promoted inputs. |

Live GitHub queries independently confirmed each listed verification job is
completed/successful and each original artifact remains unexpired with exactly
that digest and checked head SHA. The retained original ZIP bytes match those
live digests. This audit opened each ZIP without extracting/executing it and
matched every member with the retained artifact tree. The authentic result
records `comparator-accepted` and `lean_cert_proof_trust: kernel-checked` for
only the full Target export, no definition holes and the three permitted
foundational axioms.

All **325 committed/current package input hashes** matched the authentic result
manifests at the integration checkpoint, fetched candidate heads and exact
checked commits: SP-12 96, TR-14 139, PF-05 90. The exact package file sets also
match, including all **183 Lean inputs** (55 + 82 + 46). Earlier proof-only,
synthetic-merge, metadata-refresh-pending and failed boundary records remain
historical; they are not substituted for these later exact promoted-package
receipts. In particular PF-05's final receipt is retained under
`docs/lean/proofs/PF-05/verification/promotion-linux-ci/c4c7be59/`, added at
`42d16658`, even though its older top-level receipt/PR prose still requests it.

The source reviews explicitly distinguish authorship and independent scope.
Reviewers are AI agents, with no human or source-author endorsement claim. This
audit checked the actual full-target wrappers and Final modules and exact
baseline definitions, but relies on those retained full-closure semantic reviews
and authentic kernel receipts for their much larger prerequisite developments.

## TR-06 remains a substantive proof task

At `fa480595`, `docs/lean/proofs/TR-06/README.md` explicitly says no complete
Target theorem, canonical Comparator acceptance or Linux proof receipt exists.
There are 70 recovered shared support modules and retained earlier foundations.
The recovery scope JSON sets `final_Target_proved: false`. No canonical
`tensor-computations/TR-06/lean` package is present there. Controlled projection
fiber count, the graph-volume conclusion and complete Target assembly remain;
the exact canonical boundary/Solution and authoritative Linux receipt follow
only after those mathematical gates close. Preserve and reuse those recovered
sources rather than restarting the older 58-module candidate.

## Reproducibility and remaining inventory

Run `python3 reviews/2026-10-23-solved-lean/latest-candidates/audit_candidates.py`.
The script is SHA-256
`cadc0c15f8753621245c623b961e0ddf6cb56e41999e82f9cecaa9cf676ab468`;
its complete `audit.json` is
`b87bb9368fc641d62bec81a7486710e39571d877c558992fbad3bdea7dedc231`.
Saved live responses are `live-pr-info.json`, `live-workflow-evidence.json` and
`live-searches.json`; the audit does not refresh live APIs itself. The exact
source reviews, original artifact metadata, archive members and all package
input hashes are recorded in audit.json. No canonical source, registry, index,
existing dirty file or proof source was modified for this audit.

After integrating these three complete proofs, 35 Solved IDs remain:

AA-01, AV-01, AV-02, FR-10, IE-08, IE-10, IE-12, IE-21, IE-22, IV-02, IV-04,
IV-05, MD-06, MF-08, MI-16, NM-03, PF-04, RA-04, RA-05, RA-12, RA-13, RE-05,
RE-06, TR-04, TR-06, TR-08, TR-17, TR-20, TR-21, TR-26, IE-26, MI-31, RA-19,
SP-13, SP-14.
