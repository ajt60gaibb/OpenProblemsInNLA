# Independent RA-05 support Linux artifact review

Reviewer: OpenAI Codex AI agent `/root/inventory`, 23 October 2026. I authored
no RA-05 proof module or canonical package. I independently pre-reviewed and
final-reviewed both support components and the combined package. This is a
separate offline audit of the actual completed Linux artifact and its current
source correspondence.

**PASS for all eleven support exports.** Actual [run 39963923849](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39963923849),
[verification job 120449407972](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39963923849/job/120449407972),
and original [artifact 12505618149](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39963923849/artifacts/12505618149)
bind real Comparator/default-kernel acceptance and LeanCert kernel proof trust
to the exact package. **The complete RA-05 Classification and NegativeAnswer
remain unproved; canonical RA-05 remains Solved.**

## Exact execution and source identity

The actual executed GitHub PR merge is
`4c0220b702442c97e52ae98253169e6c759010bf`, whose parents are published base
`5487945e5a72abd952b0c89915915de8cc9b3e65` and PR #365 head
`0b0edfb8a75de34caec6c0f61cbf3193bbb15589`. The original raw job log explicitly
fetches/checks out that merge; authentic result.json records that same merge.
Live GitHub PR metadata independently identifies that head and synthetic merge.
The workflow API's head SHA identifies the PR source head, as expected. This
review does not relabel the actual execution as a direct head-commit run.

All **40 package inputs** and the exact complete source file set match the
result manifest at the executed merge, PR head and current canonical project in
`/Users/ajt253/.codex/worktrees/solved-lean-oct23/OpenProblemsInNLA`. The
canonical project is tracked-clean at that head. There are 13 hashed Lean files:
the eleven build/input modules and two retained historical Challenge files.
This is an input-hash count, not a claim that historical Challenge admissions
are proved theorems. The actual solution excludes Challenge from its import
closure.

The three independently approved implementation/definition files retain their
exact earlier hashes. Live definitions, separately frozen Reviewed statement,
specification, original canonical README and all 217 registered ID/path pairs
are preserved against published base. The actual canonical README is unchanged.
Published `tools/lean/` and `.github/workflows/` are unchanged too; no guard,
permitted-axiom rule or verification workflow was weakened for this package.

## Original artifact and raw-log integrity

I independently queried live GitHub job/artifact/PR metadata. The whole workflow
and selected verification job are completed/successful. The original artifact
is unexpired and has exactly the expected 16,262-byte size and digest. Its ZIP
matches both live GitHub metadata and the actual raw job's upload digest/ID.
All 15 ZIP file members match the retained extraction, with safe unique paths
and an exact file set. The raw UTF-8 log hash also matches independently.

| Evidence | SHA-256 |
| --- | --- |
| Original ZIP | `09266c552e4341bf554c2d9c553331dec0dea11c43d96a3acbd6049923acfc97` |
| Raw uncompressed UTF-8 job log | `071337faa483c1b90a514996609eb45ab095e6c676d006ad74711764eff5c2a0` |
| Retained raw-log gzip | `178fc81ff3f922d68e7d4c9c3ab88485ab835917407c63d49a8933a185033e7a` |
| Actual result.json | `f13bdad2328c947479cc8fca0a10d50f50548ee82663003337ab93a434649124` |
| Live GitHub responses | `9e841922b85dee1bc3330d77483e70f36f0ca14c06a2aed6494a5c4a8d4a66f1` |
| Independent audit JSON | `889933b11e2b78a36398e55e75d7611b95f078ec3636e0b68a5009df8d4c09e8` |

The original ZIP, compressed raw job log and raw API metadata are copied
unaltered into `retained/`. Individual artifact-member hashes, all source
hashes, live metadata and every check are recorded in INVENTORY_REVIEW.json.

## Actual selected proofs and generated kernel consumer

Comparator selects exactly these eleven advertised support theorem names, with
distinct Challenge/Solution modules, no definition holes and only the three
standard permitted axioms:

```text
NLA.Proofs.RA05.SupportMinimum.rowCost_nonneg
NLA.Proofs.RA05.SupportMinimum.cost_nonneg
NLA.Proofs.RA05.SupportMinimum.strongCoreset_one
NLA.Proofs.RA05.SupportMinimum.supportSize_one
NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_support
NLA.Proofs.RA05.SupportMinimum.minimumSupport_attained
NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_rowCount
NLA.Proofs.RA05.SupportMinimum.minimumSupport_le_worstSupport
NLA.Proofs.RA05.unitHyperplane_projector
NLA.Proofs.RA05.rowCost_unitHyperplane
NLA.Proofs.RA05.strongCoreset_implies_allVectorEmbedding
```

Both actual Comparator exports contain all eleven names, and the real default
Lean kernel accepts the solution before Comparator prints `Your solution is
okay!` and exits zero. The actual result records `comparator-accepted` and
`lean_cert_proof_trust: kernel-checked`.

I independently reconstructed the unchanged harness's deterministic consumer,
retained as `reconstructed_ProofTrustAudit.lean.txt`. Its SHA-256 is exactly the
actual receipt's
`bf044fb15f8756a47979509e9c38485431baf8487154f680d92bec834d6d9adc`.
For **each** selected name it first requires actual theorem constant kind
`.thmInfo`, then runs `#assert_trust kernel` and `#print axioms`. This checks
proved constants, rather than merely trusting a proposition definition. The
actual Linux log executes that generated consumer with AF_UNIX denied and
exits zero. All eleven transitive axiom reports contain exactly `propext`,
`Classical.choice` and `Quot.sound`.

The receipt identifies official x86-64 Linux Lean 4.33.1, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, the default verifier profile,
Forsythe checker revision `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, and
source-lock SHA
`b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`.
The real checker/exporter build succeeds, the exact ten dependency revisions
are materialized, and the real LeanCert consumer library build succeeds.

## Controls and isolation

The actual verification job executes and passes:

- All three builtin-kernel controls: honest inductive/quotient proof accepted,
  invalid raw proof rejected, and quotient post-check mismatch rejected.
- All five Comparator regressions, including mismatched statements/kinds and
  a forbidden custom axiom.
- Both build/export sandbox modes, with private namespaces, denied outside
  writes/truncation/creation and symlink writes, absent host parent access,
  denied host loopback and AF_UNIX sockets, no effective capabilities and
  `no_new_privs`. Only designated build `.lake` writes are allowed; export
  writes are denied.
- All four negative sandbox-option cases, each rejected with exit two.
- Deliberate `sorryAx` and native-evaluation axiom examples, each rejected by
  the real Comparator with exit one.

The selected workflow's separate checker-controls matrix job is skipped, but
these controls actually execute inside the successful verification job; their
raw logs and final `PASS: fresh Comparator run and all controls` are retained.
The reconstructed consumer, actual axiom reports and control logs agree with
the unchanged harness. No local mock Comparator or local macOS build is
substituted for this real Linux execution.

## Reproduce and limits

`audit_inventory.py`, SHA-256
`bba02c35c637029264f52461df40a1594bfbfe7a3bca0558c538c7727c608790`,
passes **115 explicit evidence checks**, including per-input and archive-member
checks. This count is not the historical 40/41-control count used by other
problem-specific artifact auditors. Run from the repository with the retained
artifact directory and current source worktree available:

```bash
python3 reviews/2026-10-23-solved-lean/ra05-linux-ci/audit_inventory.py
```

This audit independently checks retained genuine CI evidence and exact source
correspondence. It does not rerun Linux Comparator or Lean locally. The
receipt's execution identity is the PR merge; the head/current package is
supported by exact equality of all 40 inputs. It certifies eleven reviewed
semantic support proofs, not either complete RA-05 answer, and warrants no
canonical status promotion. No numerical certificate or external human
endorsement is claimed. Canonical files were never modified during this audit.
