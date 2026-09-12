# Verification-tool provenance and licence notices

The NLA driver (`bootstrap.sh`, `verify.sh`, `harness.py` and its tests) is
Copyright (c) 2026 George Stepaniants, licensed under Apache-2.0. It was
developed with Codex assistance. See `LICENSE-APACHE-2.0`.

`source-lock.json` fetches exact files from
[sgstepaniants/Forsythe, commit
8d1b0c0545a77b40245e84705aa7d273e6c81e62](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof).
Every fetched file has an independent SHA256 digest and byte count. No
mathematical Forsythe proof is fetched: the Lean test declarations exercise
the checker itself. Original notices and licence texts remain in place.

The fetched sources comprise:

- Lean FRO's Comparator, Apache-2.0, including the original author and
  copyright notices. Forsythe's distribution adapts the kernel replay call
  to Lean 4.33.1 and records the exact one-line change in
  `scripts/comparator-lean-4.33.1.patch`. It retains statement, transitive
  axiom, kernel replay, constructor/recursor and quotient consistency checks.
- Lean FRO's lean4export, Apache-2.0, compiled for Lean 4.33.1.
- Landrun 0.1.18, MIT, Copyright (c) 2025 Armin ranjbar; see
  `LICENSE-LANDRUN-MIT` and its original fetched licence.
- Forsythe's strict Landrun/Bubblewrap adapter and sandbox, kernel replay,
  and Comparator regression probes, under its `lean-proof/LICENSE`
  (Apache-2.0). These files are fetched without modification.

The driver derives a noninteractive CI copy of the sandbox probe: its two
systemd `--pty` options become `--pipe`, and service/caller deadlines are added.
Every assertion and isolation property remains unchanged. The original source
and its hash remain intact, and the derived source hash is checked and recorded.
The derived copy also prints each case's start for noninteractive diagnostics.

NLA adds a generic committed-project snapshot driver, recorded tool/source
hashes, configuration checks, and two additional negative controls for
`sorryAx` and Lean 4.33.1's generated native-execution axiom. NLA does not claim that the tool authors
reviewed this integration, and does not substitute Forsythe's historical
verification logs for a new run on an NLA theorem.

The licences grant code reuse; they do not establish mathematical verification
or author endorsement of NLA's results.
