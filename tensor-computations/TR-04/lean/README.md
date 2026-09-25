# TR-04 Lean formalization workspace

This folder is independent of the manuscript. `SPEC.md` is the approved
statement contract. `Challenge.lean` records the full contract for a future
Comparator run, while `Solution.lean` contains only the proved candidate-count
support lemma. The complete TT-SVD theorem is not claimed as verified.

The pinned environment is Lean `leanprover/lean4:v4.33.1`, Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert revision
`621a43d7cf21f87872392a01e874f2f1dbddc926`. Challenge.lean and Solution.lean now
compile against the local Mathlib cache. LeanCert and Comparator remain pending because
outbound GitHub access is blocked. No `sorry`, custom axiom, or native execution trust
is used in the source files.

Intended checking commands once dependencies are available:

```text
lake env lean Challenge.lean
lake env lean Solution.lean
lake env lean --trust=0 Solution.lean
```
