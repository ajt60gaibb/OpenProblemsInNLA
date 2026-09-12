# IE-18 Linux verification audit

**PASS**, reviewed 12 September 2026 by OpenAI Codex agent `/root`. The actual
GitHub Actions Ubuntu Linux run accepted all three complete-target exports.
This is a local review of an actual remote execution, not a claim that Linux
Comparator ran on the user's Mac. Independent mathematical fidelity reviews
are retained separately in the project.

The [successful run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34703657954)
checked immutable source revision `7b8512e21c50adc8597dcdbed32f2aec13c3b43e`.
The [fetch identity record](FETCH-IDENTITY.json) binds the successful verify
job, original artifact ID and SHA256, and every retained file. The original
ZIP digest was independently recomputed and matched to GitHub's digest;
every extracted member comes from that ZIP. All 43 project input hashes
match the exact committed Git blobs, including the statement and proof bytes
approved by both final referees. [The checked relationships](REVIEW-CHECKS.json)
also record the actual axiom lines and dependency pins.

The real [Comparator log](artifacts/lean-IE-18/verify-20260912T155616Z-4146/comparator.log)
is retained under the artifact's actual `verify-*` directory together with
`result.json`. The receipt identifies `NLA.IE18.residual_certificate`,
`NLA.IE18.counterexample` and `NLA.IE18.not_fourStepConjecture`, no definition
holes, and only `propext`, `Classical.choice`, and `Quot.sound` as permitted
axioms. Challenge and Solution were actually built and exported. The Solution
build reports 3683 jobs, with the actual Proof source compiled in 4.5 seconds.
All eight audited internal/public declarations report exactly the three
allowed axioms and pass their kernel trust assertions. The final log records
Lean default-kernel acceptance, Comparator success and exit zero.

The ten dependency sources were freshly cloned at the exact manifest
revisions; the official matching Mathlib compiled cache was used. LeanCert
was pinned to `621a43d7cf21f87872392a01e874f2f1dbddc926`, Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`, and Lean to 4.33.1. This does not
claim that every Mathlib dependency was rebuilt from source. The actual
tool receipt matches the previously audited checker source-lock hash,
Forsythe revision, derived CI probe and Linux checker/exporter binaries.

I read the actual isolation and rejection logs, rather than relying on the
workflow badge. Both build and export controls ran as UID 1001 with private
user, PID, mount, network, IPC and UTS namespaces, no effective capabilities
and `no_new_privs`. Outer writes/truncations and symlink escapes were denied;
the designated build write succeeded, and export writes were denied. Host
process lookup, host loopback and AF_UNIX socket access were blocked. The
nested Bubblewrap attempt executed and was stopped at UID-map setup before
its inner write. All four malformed sandbox invocations were rejected.

The honest raw-kernel fixture passed; a raw proof of False with the wrong
type and a falsified quotient constant were rejected at the expected phases.
All five full Comparator fixtures behaved as required, including statement
mismatch and custom-axiom rejection. The additional actual `sorryAx` and
Lean 4.33.1 native-generated axiom controls both failed as intended. These
failures are expected rejection tests, not failures of the mathematical run.

The source-only snapshot excludes local `.lake` artifacts and dependency
gitlinks. An earlier packaging snapshot was rejected; it is not the source
revision or verification result certified here. No mathematical source was
changed by the packaging correction.

This evidence supports the complete negative answer to the original
four-step maximum identity on the reviewed definitions. It does not verify
the source's stronger parameter family or its separate asymptotic question.
The archive and raw logs are retained so the evidence survives GitHub's
temporary artifact retention. Final publication should link this audit,
the actual comparator log and the exact immutable proof revision.
