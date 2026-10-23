# Independent actual Linux audit of RA-05 support — 23 October 2026

Reviewer: OpenAI Codex AI agent `/root/verification`, independent of both proof
implementers. **PASS: 48/48 checks, all 40 package inputs and all eleven support
exports.** This audits actual completed Linux execution; it does not claim a
proof of RA-05's complete Classification/NegativeAnswer Target.

The successful [run 39963923849](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39963923849)
and [verification job 120449407972](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39963923849/job/120449407972)
belong to PR365 head `0b0edfb8a75de34caec6c0f61cbf3193bbb15589`. The job
actually checked synthetic merge `4c0220b702442c97e52ae98253169e6c759010bf`,
whose Git parents are exactly published base
`5487945e5a72abd952b0c89915915de8cc9b3e65` and that PR head. The original
checkout log and actual harness result identify this merge. The head and merge
are kept distinct. All 40 project hashes and exact tracked file sets match the
head, actual merge and current canonical package in the RA05 worktree.

I fetched fresh GitHub connector metadata for the head's workflow runs, the
actual run's jobs and its artifact list; all relevant terminal results are
successful. Retained complete GitHub API metadata agrees with those new
observations. Original artifact `12505618149`, `lean-RA-05`, is 16,262 bytes.
Its SHA-256 is
`09266c552e4341bf554c2d9c553331dec0dea11c43d96a3acbd6049923acfc97`,
matching both GitHub metadata and the actual raw upload log. I independently
checked archive path/symlink safety, extracted it and matched every one of its
15 members to the original retained extraction. The uncompressed original job
log SHA-256 is
`071337faa483c1b90a514996609eb45ab095e6c676d006ad74711764eff5c2a0`.
The original ZIP, compressed job log, fresh connector/API metadata and exact
extraction are retained here, outside the frozen canonical project.

The actual harness says `comparator-accepted` and
`lean_cert_proof_trust: kernel-checked`. Real Comparator builds and exports
separate Challenge/Solution environments and accepts the exact eleven reviewed
support declarations with no definition holes; its default Lean kernel accepts
the solution. I reproduced the committed automatic proof-consumer generator:
its hash is
`bf044fb15f8756a47979509e9c38485431baf8487154f680d92bec834d6d9adc`,
matching the actual receipt. The generated source checks that every selected
export is a theorem constant and runs `#assert_trust kernel` on each. The actual
consumer output gives exactly `propext`, `Classical.choice`, `Quot.sound` for
every one of the eleven exports, including the multiline minimum/supremum log
entry. `ProofTrustAudit.generated.lean` retains the reproduced consumer.

I inspected the actual real Linux sandbox, raw-kernel, Comparator and rejection
logs. Honest inductive/quotient replay is accepted, an invalid raw proof is
rejected, and the quotient mismatch postcheck rejects. All five Comparator
regressions pass, including actual type/kind/custom-axiom rejection. Build and
export isolation, outside/symlink writes, private namespaces, host-network and
AF_UNIX denial, absent capabilities, `no_new_privs`, nested write rejection and
all four invalid sandbox-option cases pass. Actual sorry/native proof fixtures
are rejected with their forbidden axiom names. All dependency, service,
LeanCert-build, comparison and consumer phases have their required exit codes.
Pinned Linux Lean4.33.1/compiler, Forsythe source lock and checker/exporter/
sandbox executable identities are recorded and match the reviewed harness.

The three implementation hashes are identical to my independent source and
actual local comparison review: SupportMinimum `d21474d121f82481cf7de107ecaa8405d0b2d12cf60c08ef75fcbea471c1f0ce`,
HyperplaneDefinitions `03c589f029a146203487f4d5ed5982eb67e4a91d64c0ab8f817baf1de898a276`,
HyperplaneBridge `2e8d441f6aa46d7344c37762010be9e1afb30574e085bad980bb9bf01e7ccae1`.
The full original Target definition, canonical README and permanent-ID registry
remain byte-identical to the published base; canonical RA-05 remains Solved.
The package accurately states that its complete Target remains unproved.

`result.json` binds all checks, exact inputs, hashes and observed identities.
Reproduce this offline artifact audit from the original checkout with:

```bash
python3 reviews/2026-10-23-solved-lean/ra05-linux-ci/audit.py \
  --repo /Users/ajt253/.codex/worktrees/solved-lean-oct23/OpenProblemsInNLA
```

No proof/package byte or shared safeguard was changed. This is independent
AI-agent inspection and reproduction of actual CI evidence; it does not rerun
Linux Comparator locally or claim external human review. It verifies eleven
support results, not the entire original RA-05 problem.
