# IE-03 in Lean

Matias Andia's order-4096 Sylvester construction gives a real Hadamard matrix
with a complete-pivoting path of growth 4608. The project proves
`NLA.IE03.counterexample` and the resulting universal negation
`NLA.IE03.cryer_false`. Both are compared with the independent
[Challenge](Challenge.lean). The [numerical specification](NUMERICAL_TARGETS.md)
binds the original problem and the manuscript.

- [Path](NLA/IE03/Path.lean) composes complete-pivoting prefixes and compares
  their active squares. The latter operation permits a finite checkpoint to
  represent the active entries of an otherwise total matrix function.
- [Lift](NLA/IE03/Lift.lean) proves the two legal pivots of the order-two
  Sylvester factor, the Schur identity after the pair, and the doubled peak.
  [Walsh](NLA/IE03/Walsh.lean) proves the sign and real Gram conditions.
- [Certificate soundness](NLA/IE03/Certificate/Sound.lean) converts nonzero
  pivots, whole-square integer magnitude comparisons, and cross-multiplied
  update identities into the real Schur recurrence. The five phase modules
  use `decide +kernel` to check 124 local pivots and their exact peak values.
- [Proof](NLA/IE03/Proof.lean) checks the starting Sylvester square and the
  four bridges between phases, then combines the local traces and lifts.

The checkpoint tables use a common positive denominator and 16-bit
numerator slots. Lean decodes the slots into unbounded integers before
checking them. The Python generator reconstructs the data from the pinned
source and can compare its output with the checked-in inputs. The Lean
proof consumes the source tables and checks their arithmetic independently.

## Reproduce

The project pins Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and transitive revisions in the
[Lake manifest](lake-manifest.json). Reproducing the generated inputs also
requires Python 3.10 or newer. With both available, run:

```sh
python3 generate_checkpoints.py --check
lake exe cache get
lake build Challenge Solution
lake env lean Audit.lean
```

The two expected placeholder warnings occur in the separate Challenge build.
The Solution import closure is checked without placeholders or native
decision proofs. The two exported declarations use `propext`,
`Classical.choice`, and `Quot.sound`.

[Statement review A](reviews/statement-a.md) and
[statement review B](reviews/statement-b.md) bind the mathematical boundary.
The [local log](verification/local-build-and-axioms.log) records the macOS
build and axiom audit. Independent final reviews cover
[fidelity](reviews/final-fidelity.md), [correctness](reviews/final-correctness.md),
and [reuse and attribution](reviews/final-reuse.md).


The [isolated Linux run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/42710286364) verified both exports with the pinned
Comparator and default kernel. The [retained evidence](verification/linux-2026-11-09/README.md)
binds the checked inputs to the reviewed proof revision. To reproduce the
isolated run on Ubuntu, prepare the user systemd session and Bubblewrap as in
the [workflow](../../../.github/workflows/lean-verification.yml), then run
from the repository root:

```sh
tools/lean/bootstrap.sh /tmp/nla-lean-tools
tools/lean/verify.sh linear-systems-and-elimination/IE-03/lean /tmp/nla-lean-tools
```
