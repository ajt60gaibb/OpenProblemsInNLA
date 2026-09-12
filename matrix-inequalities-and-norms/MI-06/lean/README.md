# MI-06 Lean formalization: verified counterexample

This package formalizes Matthew J. Colbrook's fixed
rational counterexample to the [original MI-06 conjecture](../README.md).
The [complete informal source](../solution.tex) also proves a stronger
no-finite-constant result; the Lean target is the full negation of the original
universal assertion with factor `√2`.

**Status: Lean verified, 2026-09-12.** The full original target has a complete proof,
with two independent statement approvals and two independent final proof approvals.
Actual [Linux run 34711237623](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34711237623)
verified all six exports at immutable revision
`43b3dc65116633a68c32ec582fd093f3adc95597`, including real sandbox and rejection
controls, formal statement comparison and replay through Lean's default kernel.
The [independent operational audit](verification/linux-2026-09-12/OPERATIONAL-REVIEW.md)
validated all 117 source hashes and the original GitHub artifact digests. Original
ZIP archives, raw logs, receipts and all audit records are retained alongside it.

The six deliberate placeholders occur only in the statement-only
[Challenge](Challenge.lean), which the completed [proof](NLA/MI06/Proof.lean)
and [six public exports](Solution.lean) never import. All 52 actual axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`; the corresponding
kernel trust assertions passed. This is a complete verification of the original
factor-`√2` target. The stronger no-finite-constant source theorem is outside the
six formal exports.

Formalization author: **George Stepaniants**, Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA. Mathematical counterexample: **Matthew J. Colbrook**,
Department of Applied Mathematics and Theoretical Physics, University of
Cambridge. The [formalization manifest](formalization.yaml) records AI assistance,
source correspondence and independent-agent reviews; none is external human peer review.

[Definitions](NLA/MI06/Definitions.lean) retain the actual CFC matrix modulus,
the arithmetic average of left and right moduli, genuine complex unitaries,
and ordinary Hermitian PSD order. [Numerical and semantic targets](NUMERICAL_TARGETS.md)
were frozen before proof work and remain unchanged. A nonzero vector in a
two-constraint kernel avoids eigenvalue computations and unit-vector
normalization. The explicit-kernel LeanCert certificate is the exact point
inequality `2 < 9/4`; [proof-term inspection](reviews/proof-inspection.log)
confirms it is retained in the final conjecture negation.

The package pins Lean `v4.33.1`, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`; all ten dependency commits are
recorded in [the Lake manifest](lake-manifest.json). To build the complete proof:

```
lake build Solution
```

[Statement referee 1](reviews/statement-referee-1.md) and
[statement referee 2](reviews/statement-referee-2.md) approved the exact
definitions and six signatures before implementation.
[Final proof referee 1](reviews/proof-referee-1.md) and
[final proof referee 2](reviews/proof-referee-2.md) independently read the complete
proof and recompiled the target modules using separate fresh local artifacts.
Both checked all 52 standard-three-axiom reports and substantive use of the
kernel LeanCert certificate. Referee 1 also recompiled the isolated Challenge
and reran the exact rational matrix reconstruction. The implementation author
is not counted among its independent referees.

[Comparator configuration](comparator.json) selects the six exports and permits
only `propext`, `Classical.choice`, and `Quot.sound`. The actual Linux run built
Challenge and Solution in separate fresh snapshots, matched the six declarations
and replayed their exported closure through the default kernel. It cloned all ten
pinned dependencies and used 8690 official Mathlib cache files; this does not claim
that every dependency was rebuilt from source. Both real control suites ran,
including namespace/network/filesystem restrictions, malformed-kernel and quotient
controls, actual theorem mismatch and illegal-axiom controls, and explicit
`sorryAx` and native-execution rejection. The nested namespace executable ran but
UID mapping was denied before its inner write. The isolated runner's read-only
host view is a write-isolation boundary, not a general confidentiality claim.

For reproduction, start from the verified revision and satisfy the documented
[non-root Linux prerequisites](../../../tools/lean/HARNESS.md). From the repository
root, run:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-06/lean \
  /absolute/path/to/nla-lean-tools
```

Those commands require genuine sandbox and rejection controls; a local macOS
build does not substitute for that run. The manifest follows the repository's
pinned [actual v0.4 schema](../../../docs/lean/schema/README.md). Its zero proof
and definition sorry counts exclude only the deliberate independent Challenge
placeholders. No definition is replaceable by Comparator.

[Statement approvals](reviews/statement-freeze.json),
[proof completion and scope](reviews/proof-completion.md), and
[final source hashes](reviews/proof-freeze.json) record the review boundary.
Earlier attempt logs and handoff notes retain their historical pending statuses;
the final reports, independent Linux operational audit and this page state the
current verification status.
The [candidate packaging receipt](verification/linux-candidate-2026-09-12/PACKAGING.md)
records the fast-forward to the current upstream base while preserving all nine
frozen mathematical/configuration files and the original canonical source.
