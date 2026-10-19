# TR-14 canonical proof boundary under review

This directory stages the unchanged complete all-width complex Hankel target.
It currently contains no Solution and proves no catalog problem. The canonical
README retains its Solved status while the proof is developed separately.

Challenge contains one deliberate comparison placeholder and imports only the
actual statement. Identity checks equality by `rfl` with the separately frozen
statement. Comparator permits only `propext`, `Classical.choice` and `Quot.sound`
and selects exactly `NLA.TR14.target`; no support theorem can replace that export.
Solution will be added only after two independent canonical boundary approvals.

The exact target includes every m >= 3, n >= 2, all complex moment data and all
natural widths including zero, with mode-dependent ordinary factors. There is
no genericity, Vandermonde or nonzero restriction. The stronger quantitative
formula in the resolution is not substituted for the original target.

ORIGINAL.md and NUMERICAL_TARGETS.md are unchanged historical source/specification
copies, including their historical phase notices. `boundary-source-lock.json`
records the current source copies and boundary inputs before a solution exists.
Lean 4.33.1, Mathlib and LeanCert are pinned; assertions use LeanCert kernel trust.
No Linux Comparator result is claimed for this staged package.
