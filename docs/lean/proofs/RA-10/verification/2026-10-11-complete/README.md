# RA-10 completed proof: local verification

Date: 2026-10-11. Environment: macOS (`Darwin arm64`).
Branch: `codex/ra10-spectral-transfer`.
Baseline: `50106db1b75a1019b708f495db747ab37bb8efbd`. This evidence was recorded
before committing the completed proof.

From `lean-statements/`:

```bash
lake build NLA.Proofs.RA10.OperatorMonotoneRepresentation NLA.Proofs.RA10.OperatorMonotoneConcavity
```

The successful build is preserved in `complete-build.log` (3044 jobs).
`complete-source-sha256.txt` records all 97 RA-10 proof sources, the frozen
statement, and the three dependency/toolchain configuration files. Paths in
that manifest are relative to `lean-statements/`. Older evidence directories
describe earlier partial proofs and are retained as historical snapshots.

## Checked conclusions

The final module exports these unconditional theorems:

```lean
NLA.Proofs.RA10.admissibleFunction_hasCompactLoewnerRepresentation
  (hf : NLA.Statements.RA10.AdmissibleFunction f) :
  NLA.Proofs.RA10.HasCompactLoewnerRepresentation f

NLA.Proofs.RA10.transferBound_eleven : NLA.Statements.RA10.TransferBound 11
NLA.Proofs.RA10.ra10_target : NLA.Statements.RA10.Target
```

Every new theorem has a `#assert_trust kernel` check. The final representation,
transfer and target declarations report exactly `propext`, `Classical.choice`
and `Quot.sound` as their transitive axioms. The source scan found no `sorry`,
`admit`, `native_decide`, `unsafe`, `implemented_by`, or custom axiom declaration
in the RA-10 proof directory. The proof uses the existing dependencies only.

The newly discharged steps are the finite-matrix derivative formula,
Kraus-matrix sign, Loewner criterion with an exceptional scalar argument,
the needed Bendat–Sherman implication, both Hansen pieces, the harmonic
extreme-point inclusion and general representing-measure existence.
No representation, differentiability, invertibility, spectral-gap,
commutation or positive-tail assumption is added to the final target.

The frozen statement SHA-256 is unchanged:
`dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82`.
Pins: Lean 4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`;
LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`.

## Remaining verification gates

This is local kernel checking, not independent review or the repository's
authoritative isolated non-root Linux Comparator run. Both remain outstanding.
No Docker or Podman executable was available in this session. No Comparator
result or independent-review approval is claimed.

The canonical problem and its status, permanent IDs, frozen statement,
dependency pins and reviewed aggregate imports were not changed. This record
describes the local proof-completion check; the later draft PR preparation is
documented in [the review guide](../../README.md).
