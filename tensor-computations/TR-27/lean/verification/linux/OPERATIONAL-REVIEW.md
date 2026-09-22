# TR-27 complete Linux verification: operational record

Date: 2026-09-22. Operator: Codex AI agent `/root/infrastructure_audit`.
**Role: mechanical verification operator, not an independent final mathematical
referee.** I authored `NLA/TR27/ProjectiveGeometry.lean`; this report does not
claim independent review of my own proof or of the complete mathematical
correspondence. The separate nonauthor final correctness and fidelity reviews
are included in the immutable source snapshot. Earlier independent module
reviews retain their explicitly limited scopes.

**Result: the unchanged full verifier exited zero on its first attempt.**
Comparator compared all 25 frozen declarations between the separately built
Challenge and Solution modules. The authentic pinned LeanCert kernel-trust
assertions compiled for all 25 declarations, all 25 reported only the permitted
axioms, and actual Lean kernel replay accepted the complete solution. Every
real sandbox and checker control ran successfully before project verification.
No proof source, selected target, checker, sandbox assertion or control was
changed to obtain this result.

## Exact source and commit provenance

The publication source was frozen at commit
`775e8b169119c4045b07db7666eda8c001ae3bd1`, based on
`daf313133bfe730c32a266ea85cd9ca0fbe2d5ed`, in
`https://github.com/ajt60gaibb/OpenProblemsInNLA`.
The canonical project path is `tensor-computations/TR-27/lean`.

The transferred `input.tar` is exactly 583,680 bytes, SHA256
`ac04194757cbaaab666b4ae2f654a2d48078cd13f2c08a7a2eab32b0d3adb4c6`.
Its external receipt is retained as `input-receipt.json`, SHA256
`eda0ac53ffb91ebd1a894c553a56923d01d74df4ccdf78b30ed2d0c62b054958`.
Before any control or proof execution, I independently compared every one of
its 116 files with the corresponding immutable publication Git blob. The
guest then checked the archive, receipt and all extracted file hashes again.
The target list, 25 `#assert_trust kernel` commands and 25 `#print axioms`
commands agreed exactly. No `.lake` directory or compiled project artifact
was present in the transferred source.

The fresh guest repository was created under
`/home/admin/nla-tr27-full-20260922/repo`, preserving the canonical project
prefix. Its verification-only commit is
`59f8e715525a25cce2e4767a1372a94650c8071c`.
**This is intentionally a distinct local commit, not the publication commit.**
`preparation.json` records that relationship and the identical 116 source
hashes. The guest checkout was clean before and after verification. The
driver's successful result binds all 116 hashes, and a separate post-run
comparison confirmed they remained unchanged.

`source/` retains those exact original files, including the pending metadata
and source-level reviews that existed when this run began. Later publication
metadata or final referee addenda must not be described as inputs to this
earlier run. The unmodified original input archive and result receipt preserve
that distinction.

## Runtime, prerequisites and pinned dependencies

The task started the preserved `mf21-verification` VM with graphics, audio and
clipboard disabled and without a host filesystem share or configuration
change. Verification ran as guest user `admin`, UID 1000. The actual kernel
was `7.0.0-31-generic` on aarch64 Ubuntu; the prior routine guest package
upgrade became effective at this boot. Lean was 4.33.1, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; Go was 1.27.1 and Bubblewrap 0.9.0.
The non-root user systemd manager was running.

Reboot had restored `kernel.apparmor_restrict_unprivileged_userns=1`.
Before verification, the explicitly authorized, documented shared-CI
prerequisite was restored with
`sudo -n sysctl -w kernel.apparmor_restrict_unprivileged_userns=0`.
`environment-repair.json` retains before/after values and the workflow hash.
This is the same prerequisite in the repository's shared Lean CI; no sandbox
control was skipped or modified. There were no failed full-verification
attempts, transport interruptions or retries in this TR-27 run.

The existing verifier tools passed `harness.validated_tools` immediately
before the run. The guest driver, launcher and source lock matched the
publication worktree byte for byte. The source lock SHA256 is
`b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`,
pinning Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`.
The bootstrap receipt binds the actual Comparator, exporter and Landrun
binaries, the reviewed strict adapter environment and the noninteractive
probe adaptation. That receipt's platform field describes its earlier
bootstrap on kernel `7.0.0-30`; the current runtime is separately recorded
and passed every fresh control on `7.0.0-31`.

The driver created a fresh tracked-source snapshot, then materialized all ten
exact manifest revisions. While that snapshot existed, a read-only capture
checked every dependency's actual Git HEAD against the manifest. In particular:

- LeanCert: `621a43d7cf21f87872392a01e874f2f1dbddc926`.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.

The actual `LeanCert/Tactic/Verification.lean` bytes matched that pinned Git
blob and are retained in `dependency-evidence/`, SHA256
`2c576708b528acdde17796b0b715b83079f9cad377182dbd87c248323ff0a58c`.
The other eight dependency receipts are in `dependency-receipt.json` there.
The pinned Mathlib cache utility was built from this dependency source, then
decompressed 8,689 already-cached files; the log records no cache downloads.
This is the shared harness's trusted dependency-cache path, not a claim that
every Mathlib object was rebuilt from source. No project Solution build
preceded Comparator.

## Actual command and full result

The detached non-root user service `nla-tr27-full-20260922-r1.service` invoked
the retained wrapper, which ran exactly:

```bash
cd /home/admin/nla-tr27-full-20260922/repo
/home/admin/mf21-harness/tools/lean/verify.sh \
  tensor-computations/TR-27/lean /home/admin/nla-lean-tools
```

The wrapper only records execution and supplies the documented environment;
it does not alter verifier behavior or project files. It leaves dependency
cache use enabled. `service-start.json` records the requested transient
service limits. After completion systemd unloaded the transient unit, so the
default properties returned by a later `systemctl show` are not measurements
of its live limits; `service-lifecycle.json` records this and the actual
start/completion journal. The sandbox policy is separately demonstrated by
the verifier's real controls.

The run began at `2026-09-22T19:24:08.019397+00:00` and finished at
`2026-09-22T19:26:34.659940+00:00`, exit zero. Its complete log directory is
`/home/admin/nla-lean-tools/logs/verify-20260922T192408Z-961`, exported here as
`successful-verification/`.

Comparator freshly built Definitions and Challenge, with exactly the 25
intentional specification-placeholder warnings in Challenge. It exported the
complete 25-declaration list, then built all Solution proof modules and the
authentic `LeanCert.Tactic.Verification` module. Solution compiled without
warnings. The explicit `leancert.trust "kernel"` setting and all 25
`#assert_trust kernel` commands succeeded. Each explicit Solution axiom report
is exactly `[propext, Classical.choice, Quot.sound]`.

The Solution export list agrees exactly with the Challenge list and frozen
Comparator configuration. The final original-target declarations
`NLA.TR27.projective_counterexample` and
`NLA.TR27.original_conjecture_false` are included, together with every required
semantic, algebraic-image, independence and rank bridge. No auxiliary-only
selection was used.

The actual run then reported:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

`successful-verification/result.json` records `comparator-accepted`, the
complete configuration, local snapshot commit, source hashes and tool receipt.
`export-receipt.json` extracts the full actual export declaration lists from
the hash-bound Comparator log. The pinned Comparator manages and removes its
intermediate raw export streams; those streams are not represented as retained
artifacts. This report relies on its logged exports and completed comparison
and kernel replay, not on invented stream hashes.

These proofs are exact algebra, geometry and linear algebra. They need no
floating-point approximation, numerical integration or interval certificate.
LeanCert is used through its authentic kernel-trust audit commands; no
artificial numerical certificate is claimed.

## Controls and their actual scope

Both real sandbox modes completed successfully as UID 1000. User, PID, mount,
network, IPC and UTS namespaces were private. Host-process visibility and
signal lookup failed as required; host loopback was unreachable, AF_UNIX
socket creation was denied, effective capabilities were empty, and
`no_new_privs` was set. Writes, truncation, creation and symlink escapes
outside the allowed build area were denied. The designated build `.lake`
write succeeded, while export writes and truncation there failed. Fixtures
outside that permitted write remained unchanged.

The nested namespace attempt was actually launched and rejected at UID-map
setup (`bwrap: setting up uid map: Permission denied`) before an inner write.
This is its observed scope; it is not evidence of a successfully entered
nested namespace. All four prohibited adapter-option cases returned the
required rejection code two.

The three raw-kernel controls accepted the honest inductive/quotient proof,
rejected a proof of `True` supplied at type `False`, and rejected the forged
quotient after the quotient post-check. All five Comparator regressions had
their specified outcomes, including an actual theorem-type mismatch. The
retained fixture named `simple_kind_mismatch` tests an illegal helper axiom
in the pinned source; the log reports that actual behavior without relabeling
it as a distinct type-mismatch test. The separate forbidden-axiom fixtures
rejected `sorryAx` and `checked._native.native_decide.ax_1_1` with exit one.
Their expected failures are controls, not failed TR-27 verification attempts.

## Export, audit and cleanup

The guest evidence archive is 193,895 bytes, SHA256
`2a0e455491252b3b6766ba25dc566c924298868a07fa60126b23dd77f677f580`.
The host verified its exact bytes, then checked every extracted file against
its archive member. All source receipts, actual logs, dependency evidence,
runtime repair, driver/probe sources and execution records are retained here.

Run `python3 audit_evidence.py` from this directory to repeat the retained
evidence audit using the Python standard library. It checks both archive
hashes, all 116 source hashes and commit relationships, all ten dependency
heads, the pinned checker and authentic LeanCert receipts, every control,
both complete export lists, every Solution axiom report and kernel acceptance.
The audit passed; its output is `evidence-audit.log`. This checks recorded
evidence and does not replace running the shared verifier again.

After successful export and audit, the task stopped only the VM it had started.
Tart confirmed `mf21-verification` stopped, and retained boot session 20556
exited zero. `vm-lifecycle.json` records confirmation at
`2026-09-22T19:33:22.377058+00:00`. The VM disk, guest sources and logs remain
preserved. No publication action or canonical status edit was performed by
this operator; the root task retains those responsibilities after independent
final referee completion addenda.
