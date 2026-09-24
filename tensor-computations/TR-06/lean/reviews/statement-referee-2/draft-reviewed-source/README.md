# TR-06 formalization preparation — incomplete

This directory contains proposed exact definitions and independently reviewable
Challenge signatures for the original TR-06 target. It contains no completed
proof. The five `sorry` placeholders are in the trusted Challenge only; no
Solution exists and no Comparator acceptance is claimed. A successful statement
typecheck does not establish any theorem.

Read [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) before the Lean files. The full
source proof remains attributed to Matthew J. Colbrook. Formalization preparation
is credited to George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with substantial Codex assistance.

The existing shared [review protocol](../../../docs/lean/REVIEW.md) and
[Linux verifier](../../../tools/lean/HARNESS.md) remain unchanged. Proof work is
not authorized by a statement PASS until two independent reviewers have approved
the actual definitions, complete original-target correspondence and signatures.

Required foundations include semialgebraic projection/dimension/finite-volume,
real regular-locus geometry from generic complex identifiability, nonlinear
Hausdorff graph area, and polar integration on the cone. Pinned Mathlib provides
some linear volume and Gaussian integral building blocks, not those completed
bridges. The source proof requires no numerical interval certificate.

No canonical page, permanent ID, catalog status or prior verification is changed.
Publication as a fully verified problem PR must wait for all complete-target,
independent review, reproducible Linux Comparator and permitted-axiom gates.
