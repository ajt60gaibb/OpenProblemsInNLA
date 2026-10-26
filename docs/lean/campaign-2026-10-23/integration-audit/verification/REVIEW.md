# Independent promoted full-proof artifact audit — 23 October 2026

Reviewer: OpenAI Codex AI agent `/root/verification`. I authored none of these
three proofs. **PASS for reuse at integration commit
`42d1665800d0185581149ef494e03055b533d636`.** All proof-package bytes are exactly
the independently reviewed bytes executed by the respective completed Linux
jobs. No new theorem proof, source modification, canonical edit or status change
was made during this audit.

| Problem | Actual immutable Linux execution | Strict guards | Exact package / Lean inputs |
| --- | --- | --- | --- |
| PF-05 | commit `c4c7be592c51c8ba81d1579082813310a22b356d`, [run 39176870923 / job 117821318204](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39176870923/job/117821318204) | 41/41 | 90 / 46 |
| SP-12 | commit `a7adfc8e30ad284f42ec2ea0221a990ee9804031`, [run 39149417211 / job 117739903353](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39149417211/job/117739903353) | 40/40 | 96 / 55 |
| TR-14 | commit `16a1150d81f606ed6a8333be8c04730e0a477525`, [run 39174291223 / job 117814377068](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39174291223/job/117814377068) | 41/41 | 139 / 82 |

I read and freshly executed each unchanged retained `check-linux-artifact.py`
against the actual original ZIP, retained GitHub artifact/run/job metadata,
gzip-compressed raw job output and exact extraction. The archive digest matches
both the artifact metadata and the actual upload log, and every extracted member
matches the original archive. Every committed package input and exact file set
matches its executed source commit, the current package, and the selected
integration commit. The PF-05 receipt includes the final promoted package rather
than its earlier pre-promotion description. SP-12 and TR-14 likewise use their
final promoted-package receipts.

Each actual result says `comparator-accepted` and
`lean_cert_proof_trust: kernel-checked`. It selects solely the complete theorem
`NLA.PF05.target`, `NLA.SP12.target`, or `NLA.TR14.target`, with a separate
Challenge and Solution, no definition holes and only the standard three
permitted axioms. Actual Comparator/default-kernel acceptance, the reproduced
generated theorem-kind/LeanCert consumer and the actual export's printed
`[propext, Classical.choice, Quot.sound]` closure all pass. These receipts also
contain the real Linux sandbox build/export/isolation assertions, all three
builtin-kernel controls, five Comparator regressions, four sandbox-option
rejections and actual sorry/native-proof-axiom rejection controls. Checker,
exporter, sandbox binary identities, Lean4.33.1 compiler commit, Forsythe pin and
source-lock hashes are retained and matched without relaxing a guard.

I inspected the literal Target definitions and actual final proof/export modules.
PF-05 proves the full rigidity/uniqueness equivalence with arbitrary actual
factors, zeros and singular factors. SP-12 constructs the real symmetric PSD
pattern witness with full Strong Arnold property and chromatic nullity bound
for every positive-order graph. TR-14 proves the all-width ordinary/symmetric
rank equivalence for every complex Hankel tensor in the original domain,
including zero and exceptional cases. These are actual unconditional proofs of
the original frozen Target definitions, rather than Prop definitions, Identity
elaboration or conditional support reductions. Full semantic correctness and
mathematical-source attribution are supported by the separate existing
hash-bound statement and whole-source referee reports; this artifact audit does
not claim to rederive every proof module.

The additional independent integration/preservation audit passes **33/33**
checks. The complete permanent-ID registry is byte-identical to original
published base `36767fa430309f13d04dc6ebe080d470f5c2444a`, and every registered
canonical path remains present. All **171** shared-source/package-copy pairs
(42 PF-05, 51 SP-12, 78 TR-14) and all locked package exports match their
reviewed source hashes. All **13** original archived README/TeX/PDF/manuscript
objects match both their source Git objects and recorded hashes. Original
manuscripts/solutions remain in place unchanged. Removing only the delimited
formal-proof notice and restoring the explicitly changed status/date values
reproduces each original canonical README byte for byte, including all original
mathematical text, authorship and history. Each ORIGINAL.md and full Target
definition remains exact. The first preservation attempt is retained; its two
false results were caused solely by the audit's restoration code duplicating
the original Markdown trailing spaces. The corrected value-only restoration
produces exact original bytes and changes no repository input.

Receipts are `PF05-strict-replay.json`, `SP12-strict-replay.json`,
`TR14-strict-replay.json`, their execution records, and
`integration-and-preservation.json`. The reused SP-12 checker has a historical
reviewer label embedded in its report; its fresh actual executor is identified
accurately by this review and the execution wrapper. Reproduce every fresh
check from the original working checkout with:

```bash
python3 reviews/2026-10-23-solved-lean/latest-candidates/verification/reproduce.py \
  --repo /Users/ajt253/.codex/worktrees/solved-lean-integration/OpenProblemsInNLA \
  --ref 42d1665800d0185581149ef494e03055b533d636
```

This is a fresh offline audit of actual retained successful Linux executions;
it does not rerun Linux Comparator on this macOS host or claim external human
review. The shared-boundary run cancelled at TR-14's old promotion commit is
not claimed as successful. The exact full-proof jobs above and their package
inputs remain valid; an integration PR's newly triggered CI must be assessed
on its own exact commit and results. No evidence justifies claiming every
remaining Solved problem has now been proved.
