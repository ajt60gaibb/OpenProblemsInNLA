# TR-15 Lean formalization candidate

This package currently fixes and type-checks the complete original odd-order
Hankel H-eigenvalue inheritance conjecture and seven proposed proof exports.
It has no proof implementation. Two independent statement approvals are
required before writing `Proof.lean` or `Solution.lean`; the deliberate
`Challenge.lean` placeholders establish no mathematics.

The mathematical counterexample is Matthew J. Colbrook's, in the
[complete retained source](../../../references/colbrook-unclaimed-2026-09-11/manuscripts/TR-15.md).
The formalization author is George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA. This work is AI-assisted; independent review reports will
identify their actual scope. The canonical mathematical status remains
`Solved` while formal verification is pending.

- [Exact numerical and quantified statements](NUMERICAL_TARGETS.md).
- [Canonical and complete-source correspondence](SOURCE_CORRESPONDENCE.md).
- [Actual mathematical definitions](NLA/TR15/Definitions.lean).
- [Independent challenge signatures](Challenge.lean).
- [All seven registered exports](comparator.json).
- [Statement build log](reviews/statement-build.log).
- [Exact supplementary reconstruction](reviews/source-numerical-reconstruction.json).

The project pins Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. The statement-only check is:

```bash
lake build NLA.TR15.Definitions Challenge
lake env lean reviews/InspectStatements.lean
```

Future proof sources must use LeanCert's explicit kernel trust, and final
exports may depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Local macOS elaboration, independent mathematical review, and the actual
Linux sandboxed Comparator check are distinct gates. The latter has not run
for this candidate. Publication metadata and status promotion must report
only the gates actually completed.
