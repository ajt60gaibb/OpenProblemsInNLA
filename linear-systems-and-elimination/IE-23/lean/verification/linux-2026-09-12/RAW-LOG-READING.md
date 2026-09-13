# IE-23 actual runtime log inspection

Inspector: `/root/leancert_examples`, IE-23's implementing proof agent.
This records operational inspection, not another independent mathematical
review. Independent final mathematical reviewers are `/root` and
`/root/solved_statement_inventory`; `/root` separately accepts the execution
evidence. No proof, canonical entry, configuration or pin is changed here.

I read the original completed IE-23 and standalone-checker result receipts,
full Comparator log, full sandbox/kernel/Comparator-regression/native/sorry
logs in both suites, both user-service logs, dependency/cache logs and both
bootstrap logs. Initial retrieval occurred while unrelated jobs in the run
were still pending; the final verdict requires separate whole-run success.

The actual IE-23 log builds seven project modules and Solution freshly. Its
Challenge graph has 2,384 jobs, with exactly eight deliberate reference
placeholders. The Solution graph has 2,394 jobs, no admission warnings and
sixteen internal/public reports restricted to the standard three axioms.
Both exports name all eight selected declarations. Lean's default kernel
accepts the Solution, and Comparator then accepts with exit zero.
`LeanCert.Tactic.Verification` is built and the source's explicit kernel
assertions run; there is no numerical interval certificate in this pure
exact proof. The 8,690 official Mathlib cached files are reused: this does
not claim a complete dependency-source rebuild.

The two actual tool receipts agree: Lean 4.33.1 at
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Go 1.27.1,
Linux 6.17.0-1022-azure with glibc 2.39, and matching Comparator/exporter/
Landrun executable hashes. Both jobs build the pinned executable sources.
Elan says the pinned Lean toolchain was already installed by the workflow;
there is no claim that this step compiled Lean itself.

Both sandbox suites use actual non-root UID 1001, private user/pid/mount/net/
ipc/uts namespaces, no capabilities and `no_new_privs`. They deny outside
writes/truncation/creation, symlink escape, host process lookup/signaling,
host loopback and AF_UNIX socket creation. The build fixture write succeeds;
export fixture writing/truncation fails. Fixture contents are checked.
The nested Bubblewrap executable runs but fails to establish its UID map,
**before** the inner write. Its probe label must not be read as evidence
that the inner write actually executed and was separately rejected.

The raw kernel honest inductive/quotient case succeeds. A malformed raw proof
of False is rejected for a kernel declaration-type mismatch. The altered
Quot.lift case first passes kernel replay and then fails the quotient
post-check. All five Comparator fixtures build and export both environments:
the honest case reaches kernel acceptance; the `simple_mismatch` case fails
constant kind, both `simple_axiom_issue` and `simple_kind_mismatch` fail on
the actual `helper` axiom, and `type_mismatch` fails the theorem statement.
Thus the rejection descriptions follow the actual observed phases rather
than an inference solely from fixture names.

Both extra negative fixtures also build/export both environments. The
admitted proof is rejected for `sorryAx`; the genuine native proof is
rejected for `checked._native.native_decide.ax_1_1`. Their exit-one results
are expected and checked by the successful parent harness. Unsupported or
widening sandbox arguments are rejected with exit two. These exercised
probes do not assert protection against every possible sandbox attack.

I also read the actual immutable workflow and harness source for input
snapshotting, exact-pinned dependency preparation, source hashing before/
after cache and verification, tool receipt validation, default-kernel
control ordering and source-only project copying. All 58 Forsythe files
and the exact CI probe derivation are rehashed against the actual receipt.
The completed `audit_checks.py` checks and records these identities and
phases again before any final report is written.
