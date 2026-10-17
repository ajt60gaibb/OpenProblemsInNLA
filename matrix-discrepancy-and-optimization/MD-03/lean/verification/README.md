# Local verification evidence — 11 October 2026

The implementing Codex agent ran these checks on macOS with Lean 4.33.1:

- [Build](build-local.log): `Solution`, separate `Challenge`, and frozen-statement
  `Identity` targets. The single Challenge placeholder is deliberate and is not
  imported by the solution.
- [Target axiom report](axioms-local.log): `NLA.MD03.target` uses exactly
  `propext`, `Classical.choice`, and `Quot.sound`; its kernel-trust assertion passes.
- [Source correspondence](sources-local.log): unchanged reviewed statement
  bytes, toolchain, exact dependency revisions, clean dependency tracked files,
  and external Komlós source hashes.
- [Metadata](manifest-local.log): pinned v0.4 schema and complete Comparator
  target coverage.

[local-result.json](local-result.json) records the actual commands, return codes,
compiler version and project source hashes. The local build reused the existing
pinned macOS Mathlib cache; the external proof source and new modules were
compiled locally. This is not a fresh isolated verification run.

The retained [local verifier attempt](linux-precondition.log) stopped at its
Linux precondition. A later [GitHub Actions isolated Linux verification
job](../../../../docs/lean/proofs/MD-03/LINUX_CI_RECEIPT.md) passed Comparator,
the default Lean kernel, LeanCert trust checks, and the axiom audit. To reproduce
on a suitable non-root Linux host, from the repository root:

```sh
bash tools/lean/bootstrap.sh /tmp/nla-md-checker
bash tools/lean/verify.sh matrix-discrepancy-and-optimization/MD-03/lean /tmp/nla-md-checker
```

The [independent proof and wrapper review](../../../../docs/lean/proofs/MD-03/INDEPENDENT_REVIEW.md)
and the earlier statement reviews are described in
[../reviews/README.md](../reviews/README.md). The catalog status is Lean verified.
