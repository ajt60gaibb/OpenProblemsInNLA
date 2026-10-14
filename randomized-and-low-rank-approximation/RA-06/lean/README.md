# RA-06 full-target Lean proof

This self-contained Lean 4.33.1 project selects one Comparator theorem,
`NLA.RA06.target : NLA.Statements.RA06.Target`. `Solution.lean` exports the
proved theorem `NLA.Proofs.RA06.target`; `Challenge.lean` is the isolated
intentional hole. The target is the complete frozen negative RA-06 assertion,
not a fixed-parameter witness or a conditional helper result.

The two statement modules and fourteen proof modules under `NLA/` are copied
byte-for-byte from `lean-statements/NLA/`. `ra06-source-lock.json` records all
sixteen original paths and SHA-256 hashes. The shared validator rejects any
missing, changed, symlinked, or extra copied module. The project pins Lean,
Mathlib, and LeanCert in its toolchain, Lakefile, and manifest. Build caches are
excluded from Git.

Local check:

```bash
lake build Challenge Solution LeanCert.Tactic.Verification
```

The shared Linux verifier snapshots committed project files, runs the
source-lock check, runs pinned Forsythe Comparator in isolation before building
`Solution`, and then runs a generated `#assert_trust kernel` LeanCert audit on
the selected theorem.
