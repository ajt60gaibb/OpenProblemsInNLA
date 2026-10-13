# Local verification evidence — 11 October 2026

The implementing Codex agent ran these checks on macOS with Lean 4.33.1:

- [Build](build-local.log): the MD-03 bridge, MD-03-to-MD-04 reduction, complete
  `Solution`, separate `Challenge`, and both frozen-statement identities.
- [Target axiom report](axioms-local.log): `NLA.MD04.target` uses exactly
  `propext`, `Classical.choice`, and `Quot.sound`; its kernel-trust assertion passes.
- [Source correspondence](sources-local.log): both unchanged reviewed statements,
  the byte-identical MD-03 bridge, toolchain, pinned dependency revisions, clean
  dependency tracked files, and external Komlós source hashes.
- [Metadata](manifest-local.log): pinned v0.4 schema and complete Comparator
  target coverage.

[local-result.json](local-result.json) records the actual commands, return codes,
compiler version and project source hashes. The existing pinned macOS Mathlib
cache and compiled dependency modules were reused. This is not a fresh isolated
verification run. The sole deliberate Challenge placeholder is never imported
by the solution.

The [authoritative verifier attempt](linux-precondition.log) stopped at its
Linux precondition. No sandbox substitute or Comparator success is claimed.
On a suitable non-root Linux host, from the repository root:

```sh
bash tools/lean/bootstrap.sh /tmp/nla-md-checker
bash tools/lean/verify.sh matrix-discrepancy-and-optimization/MD-04/lean /tmp/nla-md-checker
```

Independent review of the new proof and Challenge wrapper is also pending.
The existing independent statement reviews and their limitations are described
in [../reviews/README.md](../reviews/README.md). No catalog status was promoted.
