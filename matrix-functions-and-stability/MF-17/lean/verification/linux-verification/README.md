# Complete isolated Linux run

**Result: PASS; overall harness exit status 0.** Run directory:
`verify-20260930T133910Z-9471`, 30 September 2026 (UTC).
The [driver log](driver.log) records the complete run and observed exit status;
[result.json](result.json) is the unchanged harness-generated receipt.

The input was local commit `ac582d01532a914538cbfb74863437b18433038a`.
The receipt selects exactly the five declarations in `../../comparator.json`,
with no definition holes and only the three standard permitted axioms.
Both the statement comparison and Lean's default-kernel replay passed.
The earlier standalone [axiom report](../axioms.log) prints each target's
transitive axioms explicitly.

The runner was native Ubuntu 26.04 aarch64, using a private filesystem,
user/PID/mount/cgroup namespaces, a real systemd init and user service manager,
and a non-root verifier account. It exposed no host credential directories.
The [environment record](environment.txt) identifies Linux, systemd and Lean.
The user manager can report `degraded` after the deliberately failing
negative fixtures; their expected rejection is verified by the control logs.
This was a local native run, not hosted CI or the earlier emulated VM attempt.

The original pinned checker/exporter/Landrun binaries and source lock were
validated by the unchanged harness. The actual controls are retained:
[user service](user-service.log), [sandbox](sandbox.log),
[kernel replay](kernel-controls.log), [Comparator regressions](comparator-controls.log),
[`sorryAx` rejection](negative-sorry.log), and
[native-trust rejection](negative-native.log).

## Resource accommodations

The systemd user manager used `DefaultLimitNOFILE=65536:65536`.
The toolchain's executable/imported libraries, newly fetched dependency
checkout, and all compiled proof libraries resided on native Linux storage.
The committed source checkout and compressed cache were on the larger local
volume. An unused static linker archive was also backed by that volume at
its unchanged read-only runner path; its bytes were not altered.

The fresh project's initially empty `.lake/build/ir` directory was backed
by a separate directory on the larger volume. It contained only newly
generated C/setup outputs; no previous MF-17 outputs were reused. Imported
`.olean`, `.olean.private` and Lean `.ir` libraries remained on native storage.
The ordinary sandbox still controlled the same logical `.lake` write scope.

The [one-run resource helper](resource-control.py) used standard OS
stop/resume signals to permit at most two active Lean compiler processes.
Its [actual log](resource-control.log) records 206 compiler pauses and the
resumption of surviving paused processes. It detached the generated-output
mount immediately after the Solution build succeeded, before proof export,
kernel replay and fresh-copy cleanup. It edited no proof, statement,
checker, source pin, axiom rule or verification result.

The unchanged authoritative command was:

```sh
python3 /home/verifier/repo/tools/lean/harness.py verify \
  /home/verifier/repo/matrix-functions-and-stability/MF-17/lean \
  /tmp/mf17-nla-tools
```

These storage/job-control accommodations addressed this machine's limits.
On an ordinary non-root Linux runner with sufficient native storage and
memory, use the repository's documented bootstrap/verify commands directly.
