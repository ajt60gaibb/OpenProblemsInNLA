# Fresh verification infrastructure review — 23 October 2026

Reviewer: OpenAI Codex AI agent `/root/verification`. This independent
infrastructure/runtime work changed no canonical page, published ID, original
source, shared checker, or index. It supplies local controls and exact support
proof comparisons; it does not complete any remaining NLA Target.

The frozen published baseline is `5487945e5a72abd952b0c89915915de8cc9b3e65`.
The working checkout remains the older `286d8768fbd9a69264daa88e285680293db29837`
with pre-existing changes. All shared-tooling checks used the newer published
sources retained in `published-tooling/`, whose input manifest is
`published-tooling-snapshot.json`. The older checkout's harness must not replace
the published automatic theorem-kind/LeanCert export audit.

| Freshly executed gate | Result and retained receipt |
| --- | --- |
| Published portable harness tests | **15/15 passed**, `published-harness-tests.json` and `.log` |
| Pinned Comparator library fixture assertions | **9/9 passed**, `comparator-core/attempt-_9tu461s/result.json` |
| LeanCert/runtime/rejection controls | **7/7 passed**, `kernel-probes/attempt-eu__hx0d/result.json` |
| Actual eleven RA-05 support exports | **22/22 statement/axiom checks passed**, 16 Lean commands, `actual-comparisons/attempt-yiz5d36d/result.json` |

The Comparator fixtures reject mismatched theorem types, changed definitions
behind the same type, theorem/axiom-kind replacement, admitted proofs and native
proof axioms. The LeanCert controls separately accept an exact rational proof,
reject sorry/native proofs, and use the actual published generated audit to
reject a Prop definition advertised as a proved theorem. A deliberate shared
Linux selftest invocation on this macOS host fails closed with exit 2 and its
explicit Linux requirement; no fake sandbox or policy workaround was used.

The successful numerical control is an actual proof of
`Real.log 2 < (7 : ℝ) / 10`, using both global kernel mode and explicit
`leancert (trust := kernel)`. I compiled the complete **131-module** pinned
LeanCert tactic closure into an owned temporary tree, then compiled this
fixture, applied `#assert_trust kernel`, and printed the actual proof's axiom
closure: exactly `propext`, `Classical.choice`, `Quot.sound`. The receipt retains
137 command records, all 131 source digests, raw logs and source snapshots.
All ten dependency Git revisions and tracked-source cleanliness checks passed
before and after; no other worktree's dependency objects were written. The
temporary compiled objects were removed. Earlier owned-builder failures are
retained in `attempt-0bp76r96` and `attempt-n120wrcl`; corrected prefix lookup
and import-header parsing resolved those development failures without changing
any pinned Lean source or safeguard.

The exact support proof review is in
[`RA05-SUPPORT-FINAL-REVIEW.md`](RA05-SUPPORT-FINAL-REVIEW.md). It binds actual
implementation bytes, both independently approved Challenges, the exact
published RA05/RA06 definitions, and the separate-environment comparison. Each
of the eleven actual exports passed the generated theorem-kind/kernel-trust
consumer with exactly the standard three axioms. These are minimum-support and
hyperplane-transfer results; they establish neither RA-05 Classification nor
its universal NegativeAnswer. Canonical status must remain Solved.

## Pins and reproducible commands

Default pins are Lean **4.33.1**, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`; Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`; Forsythe checker sources
`8d1b0c0545a77b40245e84705aa7d273e6c81e62`. The checker source-lock SHA-256 is
`b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`.
The separately reviewed MF-23 profile retains its own 4.34.1 pins.

The previous October 17 executable path had been emptied. I restored the
official arm64 Darwin release into
`/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64`. Its 556,491,708
byte archive SHA-256
`88c45aad985b5d2a8d925fe10bd1296bd35f66f408480ab182d3facccd065a9d`
matches the original GitHub asset metadata retained in `lean-release-v4.33.1.json`.
`runtime-receipt.json` records archive URL/hash, exact executable hashes and
version outputs. Download that exact official archive, verify this digest,
then extract it with `tar --zstd -xf` if the temporary runtime moves or expires.

From the repository root:

```bash
python3 -m unittest discover -s reviews/2026-10-23-solved-lean/verification/published-tooling/tools/lean -p 'test_harness.py' -v
python3 reviews/2026-10-23-solved-lean/verification/check-comparator-core.py --lean /private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean
python3 reviews/2026-10-23-solved-lean/verification/run-kernel-probes.py \
  --lean /private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean \
  --packages /Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages \
  --build-numerical
```

The final support review provides the exact actual-comparison invocation. These
recipes take explicit runtime/cache paths, freeze the selected source bytes and
retain new attempt receipts. Development compilation trusts the pinned external
dependency object cache; it is not a fresh rebuild of Mathlib or Lean itself.

## Required authoritative Linux evidence

This host is macOS arm64 and lacks systemd-run, Bubblewrap, Go, elan and a Linux
container runtime. The successful local checks do not execute the Linux
Comparator executable, exporter, real sandbox or separate raw-kernel replay.
For an immutable committed proof package, use the current published tooling
on the required credential-free, non-root Linux runner:

```bash
python3 tools/lean/validate_manifest.py category/ID/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh category/ID/lean /absolute/path/to/nla-lean-tools
```

Require actual `result: comparator-accepted` and
`lean_cert_proof_trust: kernel-checked`, selected theorem/source correspondence,
all sandbox/kernel/Comparator/rejection logs, immutable commit/run/job/artifact
identities and hashes, then independent artifact review. The published workflow
already supplies this path; local controls do not waive it. Old successful
receipts apply only to their exact input bytes. In particular latest main
already retains the complete SP-11 receipt for commit `9264361fafb89b37b5c48236afebb304bc84110a`,
run `39131755109`, job `117688269984`; its own text correctly requires fresh CI
for later changed package inputs. I read that receipt but did not replay its
Linux artifact in this subtask.

No numbering validator or catalog generator was run here because no canonical
publication or index change was made. The maintainer's permanent-ID checks and
full informal-statement/proof reviews remain required at publication.
