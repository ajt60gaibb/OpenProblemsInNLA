# MF-12 independent batch8 repair addendum

**Approve the two source repairs.** The complete mathematical-source approval
extends to the new PowerBounds and JordanBounds hashes in `CHECKS.json`.
This remains source-only approval of those repairs; complete verification and
their actual rerun are pending. Reviewer `/root/next_elimination` is independent
of implementation author `/root/next_matrix_functions`.

I read the actual run35032749668 errors, checked the full log hash, and compared
the exact before/after files against the existing reviewed snapshots.
PowerBounds now changes the already definitionally equal expression to
`|loss q|` before applying its nonnegativity lemma. JordanBounds substitutes
m=0 before simplifying the zero-exponent branch (whose matrix dimension is one), and specifies
the real cast in the nonnegative binomial-coefficient proof. The bounds,
matrices, assumptions and small-length cases are unchanged. No mathematical
new step or target weakening is introduced.

All nineteen current project sources are bound in the receipt; only these two
files differ from the prior repair snapshot. All 28 exported types and the
frozen Definitions/Challenge/numerical boundary still match exactly. The actual
preceding run accepted RootLimit, Gaps and JordanEntries after their earlier
repairs, and also accepted GapBounds. PowerBounds and JordanBounds failed;
their dependent complete assembly remains unaccepted. No local Lean/Lake/build
command was run. Actual full compilation, transitive axioms, LeanCert,
Comparator/default-kernel replay, rejection controls and final independent
referees remain required; no verified-problem count is increased here.
