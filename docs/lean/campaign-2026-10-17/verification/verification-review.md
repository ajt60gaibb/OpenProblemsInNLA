# Verification infrastructure review — 17 October 2026

Reviewer: `/root/lean_verification`, independent Codex AI agent. This is an
infrastructure/runtime review, not human peer review or a mathematical approval
of a new problem proof. No canonical problem, published ID, existing proof, or
shared verification script was changed.

## Baseline and existing evidence

The initial checkout is old (`286d8768`, `codex/ie23-author-history`). Its dirty
canonical files are pre-existing work. The campaign should use published
`origin/main` revision `47006df8` (full revision is recorded in
`verification-evidence/result.json`) in its own worktree. In particular, the
current checkout's `tools/lean/harness.py` predates the automatic LeanCert
proof-export audit; copying it into a new campaign would lose a required gate.

At that published baseline FR-05 already has a completed proof, independent
review, canonical `Lean verified` status, and an isolated Linux receipt:
`docs/lean/proofs/FR-05/{INDEPENDENT_REVIEW,LINUX_CI_RECEIPT}.md`. The receipt
records [run 38000947893, job 114058782811](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38000947893/job/114058782811),
merge revision `e70f6976c51d4ef1246b395aeb0ff0678b9483e1`, PR head
`1d262c8609a6ba3cfd85989fa8ac1317a04fec93`, artifact `lean-FR-05`, and
`result = comparator-accepted`, `lean_cert_proof_trust = kernel-checked`.
The four selected proved theorem exports include the original all-signals
Gaussian limit `phaseRetrieval_injective_probability_tendsto_zero` and the
stronger `phaseRetrieval_injective_probability_le_inv`. All four axiom closures
are exactly `propext`, `Classical.choice`, and `Quot.sound`. The initial
infrastructure review read the published receipt and source. The subsequent
artifact audit below independently downloaded and checked the actual logs,
without rerunning Lean. Preserve that exact evidence and avoid reimplementing
FR-05.

`docs/lean/proofs/INVENTORY.md` at this baseline identifies 5 complete original
targets, 9 partial projects, and 33 statement-only targets from the previous
47-problem campaign. It is a source inventory, not an authoritative current
queue: newer PF-05, RA-19, RA-10, TR-14, TR-06, MD-03 and MD-04 worktrees or PRs
must be inspected before choosing new implementation ownership.

## Exact-statement and proof gates

The applicable policies are `CONTRIBUTING.md` § Lean verification,
`docs/lean/README.md`, and `docs/lean/REVIEW.md`. Preserve the original mathematical
target, canonical README path, original problem/solution sources, attribution,
and every registered ID. A definition `Target : Prop`, a type-checked Challenge
with reference holes, or `#assert_trust kernel Target` does not prove Target.

For every new complete proof:

1. Freeze the canonical problem, full informal proof, exact constants and
   quantifiers in `NUMERICAL_TARGETS.md`, definitions, and independent Challenge
   signatures. Record the actual source bytes and SHA-256 digests.
2. Obtain two independent statement approvals before implementation. Definitions
   and imported semantics must be inspected. Any mathematical boundary change
   reopens review; pre-existing drafts with known semantic gaps cannot simply be
   filled in and labelled faithful.
3. Prove the same fully qualified theorem names in a separate Solution
   environment. Solution must not import Challenge. Supply every additional
   premise rather than exporting a conditional reduction as the original result.
4. Put every advertised theorem in `comparator.json`, with distinct Challenge
   and Solution modules, `definition_names: []`, and permitted axioms contained
   in `propext`, `Classical.choice`, `Quot.sound`.
5. Independently review final fidelity/scope, proof correctness, and
   reuse/clarity/attribution. Reports must bind actual final hashes, identify AI
   reviewers, and resolve prior substantive findings.

Keep the pinned default Lean `leanprover/lean4:v4.33.1`, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, unless an independently reviewed
compatibility requirement calls for another supported profile. MF-23 alone has
the existing 4.34.1 profile. The initial checker accepts TOML Lakefiles and exact
HTTPS GitHub dependency revisions in a committed `lake-manifest.json`, with no
local path dependencies or replaceable definition holes.

LeanCert defaults to native trust. Numerical certificates must use both
`set_option leancert.trust "kernel"` and explicit `leancert (trust := kernel)`;
`auto` is insufficient because it can fall back to native verification. Use
`#assert_trust kernel` and `#print axioms` on each actual proved export. Exact
algebraic arguments need no artificial numerical certificate.

## Available local runtime

The shell PATH has no `lean`, `lake`, or `elan`; a working installation exists:

```text
/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin/lean
/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin/lake
```

The Lean binary reports version 4.33.1, arm64 Apple Darwin, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. An existing package cache is:

```text
/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages
```

All ten cached package Git revisions match published
`lean-statements/lake-manifest.json`; tracked sources were clean before and after
the probe. Mathlib and its relevant dependency objects exist. LeanCert currently
has its `LeanCert.Tactic.Verification.olean` built, but not
`LeanCert.Tactic.LeanCert.olean`. Consequently ordinary proofs and LeanCert
proof-trust assertions can run immediately; actual numerical `leancert` calls
need the numerical tactic module and its dependency closure built in an owned
temporary project. Do not write build artifacts into the other PF-05 or TR-14
agents' worktrees. Direct Lean compilation with a fresh output prefix and
read-only dependency `LEAN_PATH` is the established local pattern in KE-04,
IS-02, and IE-06. Compiled dependency caches remain trusted local inputs.

`verification-probe.py` reproduces a positive rational proof audited by
LeanCert kernel trust, plus deliberate sorry/native rejection controls. It
also probes and records the currently missing numerical-tactic object. Run:

```bash
python3 docs/lean/campaign-2026-10-17/verification/verification-probe.py
```

The source fixtures, raw Lean output, version and executable digest, exact
commands, and before/after dependency reports are retained under
`verification-evidence/`. This is a local runtime control, not an NLA proof,
fresh dependency rebuild, full Comparator run, exporter run, or isolated Linux
verification. The reusable script should be adjusted if its runtime/cache paths
move; no network installation was attempted.

## Authoritative reproduction and CI evidence

Use the latest `tools/lean/` and workflow from the published baseline. On a
credential-free, non-root Linux runner with the prerequisites in
`tools/lean/HARNESS.md`, after the self-contained proof project is committed and
unchanged:

```bash
python3 tools/lean/validate_manifest.py category/ID/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh category/ID/lean /absolute/path/to/nla-lean-tools
```

The shared controls include the real sandbox probe, three raw-kernel controls,
five original Comparator controls, and sorry/native rejection controls. Each
verification repeats these controls before proof work. It snapshots ordinary
tracked project files from HEAD, materializes exact public dependencies, checks
input hashes, and invokes real Comparator inside the AF_UNIX-restricted
systemd/Landrun/Bubblewrap service before any Solution build in that fresh
directory. It accepts only standard foundational proof axioms.

After Comparator acceptance, the published harness builds the pinned
`LeanCert.Tactic.Verification`, generates `ProofTrustAudit.lean` from the exact
Comparator selection, requires each selected name to be a theorem constant,
and runs its kernel trust/axiom audits in the same restricted service. Retain
`result.json`, `comparator.log`, `leancert-build.log`,
`leancert-proof-trust.log`, all rejection controls and bootstrap receipts. An
authoritative complete default-profile receipt must say
`result: comparator-accepted` and `lean_cert_proof_trust: kernel-checked`.

`.github/workflows/lean-verification.yml` already selects changed registered
projects, validates metadata, installs exact Go/Lean tooling on Ubuntu 24.04,
prepares the real user systemd service, and uploads logs as `lean-ID`. A committed
proof PR triggers its own verification; `workflow_dispatch` selects all current
projects. Metadata validation and the selector's removal safeguards must remain
enabled. Preserve an immutable proof commit, run/job links, downloaded artifact
hashes, per-input correspondence, and the transitive axiom output. Old green
logs apply only to their recorded source bytes.

This host is macOS arm64; no Docker, Podman, Lima/Colima, Bubblewrap, or systemd
executable was found on PATH. The authoritative shared harness intentionally
rejects macOS. A local Comparator-library comparison of separate Lean
environments can be useful development evidence, as IE-06 demonstrates, but
does not supply Linux isolation, exporter execution, or separate raw-kernel
replay. Use the existing hosted Linux workflow for those gates.

Before a final status/index publication, also run the permanent-ID validator,
catalog generator, and ID tests with `--base-ref origin/main`, as required by
AGENTS.md. Promotion requires full target correspondence and evidence, canonical
README and RESOLVED links to immutable proof sources, and synchronized TeX/PDF
and catalog updates. An incomplete proof retains the appropriate existing
mathematical status and states its actual formalization scope.

## FR-05 historical artifact audit

The original `/private/tmp/nla-fr05-ci-pr342` directories were empty, so the
existing `lean-FR-05` artifact was downloaded again with `gh run download`.
`check-fr05-artifact.py` passed all **33 checks**. All **154 historical project
input hashes** match both published `47006df8b3a6c724a557266c891893d03e69323a`
and the campaign worktree, with the identical complete project file set. The
four key log/result hashes match the published FR-05 receipt. The checker
source lock and reconstructed generated proof-audit source hash also match.

The actual artifact retains successful Comparator/kernel/sandbox controls,
the required sorry/native rejections, the selected four theorem axiom reports,
and the `comparator-accepted` / `kernel-checked` result. GitHub metadata confirms
FR-05 job **114058782811 succeeded**. The overall multi-project workflow was
cancelled after other jobs were stopped; its overall conclusion must not be
described as successful.

`fr05-artifact-check.json` records the per-file comparisons and limitations;
`fr05-run-metadata.json` retains concise GitHub job metadata;
`fr05-linux-artifact/` retains the actual downloaded logs. Reproduce offline:

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-fr05-artifact.py
```

This is independent verification of a historical Linux result's integrity and
exact current source correspondence, not a new Linux execution or a new
mathematical statement review. No rerun is needed merely to establish whether
these unchanged bytes have existing FR-05 proof evidence.
