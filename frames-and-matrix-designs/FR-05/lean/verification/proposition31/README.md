# Proposition 3.1 verification

Lean 4.33.1 (`819816b2e0a3bf405af45ae5cc7af2491d8f5bee6`), WSL Ubuntu x86_64.
Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.

The ten new modules were checked individually with:

```sh
lake env lean -o .lake/build/lib/lean/NLA/FR05/<module>.olean NLA/FR05/<module>.lean
```

All ten checks passed without warnings. Missing or stale prerequisite modules,
the public `NLA.FR05.Proof` boundary, and `Solution.lean` were also checked.
Some unchanged prerequisites retain their existing linter suggestions.
No `lake build` was run.

`source-sha256.txt` records the 169-module public import closure.
The preceding Proposition 3.2 manifest also verified unchanged.

`lake env lean verification/proposition31/Inspect.lean` produced `check.log`.
All 46 audited declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`. The audit covers every explicitly named declaration in the
ten new modules, together with `proposition_3_2`. No `sorry`, `admit`, or
new axiom occurs in the new sources.

The two Proposition 3.1 endpoints are:

- `proposition_3_1`: the canonical iid planted law;
- `proposition_3_1_haar`: its independent Haar orientation.

Both use the original `PhaseRetrievalInjective` predicate and assert an
eventual `C/M²` bound. Their proof supplies `C = 113`.
See [PROPOSITION_3_1.md](../../PROPOSITION_3_1.md) for the numerical choices
and the separate final FR-05 assembly still outstanding.
