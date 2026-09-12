# Pinned Linux Comparator harness

The entry points are:

```bash
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh category/ID/lean /absolute/path/to/nla-lean-tools
```

The tool directory should be outside all problem projects. The bootstrap
fetches 58 exact files (about 200 KB) from the immutable Forsythe revision
in `source-lock.json`, verifies every SHA256 digest, and builds the actual
checker, exporter and Landrun. It does not download a Forsythe proof.

Prerequisites are non-root Linux, Python 3, Git, elan, Go >=1.24, a C
compiler, `/usr/bin/bwrap`, unprivileged user/mount namespaces, and a working
user systemd service/session. Bootstrap selects Lean 4.33.1 through elan.
Go uses the supplied go.mod/go.sum and `-mod=readonly`; its actual version
is recorded. The Linux host must allow the real sandbox probe to pass.
Neither entry point provides a fake sandbox or an authoritative macOS path.
An ordinary `lake build Solution` on macOS remains a separate developer check.

The verifier takes a **committed**, unchanged, self-contained project. It
copies ordinary tracked files directly from the repository's HEAD into a
fresh directory, rejecting symbolic links and compiled build artifacts.
Only a TOML Lakefile and committed manifest with exact HTTPS GitHub git
dependencies are currently supported. No local path dependencies or
definition holes are accepted in this initial integration. A separate
reviewed extension can support those when needed.

`selftest.sh` checks the infrastructure without proving an NLA theorem.
It runs the same shared controls that `verify.sh` runs before each project:
the preserved sandbox probe, three kernel replay controls, five original
Comparator controls, and negative controls for `sorryAx` and native trust.
The native fixture computes `(List.range 37).reverse.length = 37`; Lean
4.33.1's `#print axioms` confirms that `native_decide` introduces the
forbidden fresh axiom `checked._native.native_decide.ax_1_1` for this proof.
The allowlist also excludes the older generic `Lean.ofReduceBool` axiom.

Before any NLA Solution is built, the project verifier runs those controls. It then
materializes the pinned dependencies and obtains the trusted Mathlib cache,
checks that the committed inputs did not change, and invokes Comparator
inside the AF_UNIX-restricted systemd service with real Landrun/Bubblewrap
isolation. There is no preceding Solution build in that fresh directory.
The exact allowed axiom set is a subset of `propext`, `Quot.sound`, and
`Classical.choice`; custom and native-execution trust axioms are forbidden.

If a cache is unavailable, explicitly set `NLA_LEAN_SKIP_CACHE=1` to request
a source build. This changes build cost, not the statement, proof, axiom
policy or sandbox. Network is used during public dependency preparation;
the proof build and export run without network. The driver does not read
or copy credentials and removes authentication environment variables.
As in Comparator's published trust model, the infrastructure, Challenge,
Lakefile, dependencies and toolchain must be trusted separately.

Logs are retained under `TOOL_DIR/logs/verify-<UTC>-<PID>/`. A successful
`result.json` identifies the repository commit, project, selected declarations,
source hashes and tool receipt. Any nonzero result is a failed or incomplete
verification; it must not be labelled verified. Exit 2 also covers missing
host prerequisites. Existing successful logs do not make a later failed
run pass.

The command checks formal statement equality, the axiom closure and kernel
acceptance. It does not perform informal-statement review, metadata-schema
validation, source attribution review or the repository's complete-target
audit. Those are separate required gates.

On hosted CI, prepare the user systemd session and required namespaces
before invoking the scripts. A generic Linux container without a working
user service manager is insufficient. The sandbox probe fails closed when
the required isolation is unavailable. See `NOTICE.md` for exact provenance.
