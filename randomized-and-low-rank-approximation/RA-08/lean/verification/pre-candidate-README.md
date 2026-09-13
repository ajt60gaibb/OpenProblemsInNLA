# RA-08: statement-stage Lean formalization

**This package contains definitions and fourteen proposed theorem statements;
it contains no completed proof.** The first fresh statement checks passed, but
two independent statement approvals, implementation, final proof reviews and
actual Linux verification are all pending. The canonical entry remains
**Solved** on its existing informal proof. No status or index is changed here.

Formalization: **George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA**, with
AI-agent assistance. **Matthew J. Colbrook**, Department of Applied Mathematics
and Theoretical Physics, University of Cambridge, retains mathematical
authorship of the source counterexample. Persson, Meyer and Musco retain the
original question's attribution. No contact email is added.

[Definitions](NLA/RA08/Definitions.lean) retains the entire original universal
RA-08 statement, including the actual real PSD order, Euclidean operator norm,
continuous nonnegative nondecreasing concave scalar functions on the half-line,
and every permitted ordered orthonormal eigenbasis. The same chosen eigenvectors
are used in the two truncations. Generic `f(0)=0` and operator monotonicity are
not assumptions. The actual CFC, existence of ordered decompositions and exact
truncation semantics have separate visible theorem obligations.

[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) records the unchanged rational
6-by-6 source witness with `t=1/65536`, an exact polynomial minorant, the three
matrix-vector products and the precise positive rational gap. This route would
avoid the source's contour estimate while proving the same full negative
answer. The stronger informal numerical ratio is outside the proposed exports.
The source's original target and evidence are untouched.

[Challenge](Challenge.lean) contains exactly fourteen intentional placeholders.
They prove nothing and must never be imported by the future Solution. The
[Comparator configuration](comparator.json) lists all fourteen planned exports,
no definition exceptions and only the three standard axioms. It has not been
run on a solution; no Solution or Proof file exists yet.

The local author runner
[run_statements.py](reviews/statement-evidence/run_statements.py) uses Lean
4.33.1 with a fresh private target prefix and only the ten clean pinned MI-22
dependency objects read-only. It copies no dependency cache, runs no Lake build,
and excludes all old project objects. The raw attempts retain the initial
explicit-CLM-parameter elaboration correction and the subsequent successful
three-command run. The inspector checks the actual definitions and imported
instances; definition-only `#assert_trust kernel` checks do not certify any of
the fourteen proposed theorems.

On a normal checkout with its own dependencies, `lake build Challenge` checks
statements only. Local constrained-disk reproduction uses the recorded direct
runner and paths. Do not run the completion-only manifest/Comparator gate on
this statement package or describe a challenge-only build as a proof. The
actual [v0.4 manifest](formalization.yaml) reports pending scope and no main
proved results; only the upstream JSON schema applies at this phase.

Pins are Lean **4.33.1**, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`; all ten transitive pins are in
[lake-manifest.json](lake-manifest.json). The planned sole numerical certificate
is the strict rational scalar gap using explicit kernel LeanCert on a singleton,
with its term materially consumed by the final result. No interval around an
eigenvalue or matrix entry is proposed.

[SourceCorrespondence.md](SourceCorrespondence.md) maps the complete source to
the formal boundary and records the root coordinator's compression-route
contribution. The statement author agent is `/root/formal_review_standards`;
root and `/root/solved_statement_inventory` are assigned statement referees.
Final proof reviewers must be independent of the eventual mathematical authors.
The campaign follows the [Tau Ceti-based protocol](../../../docs/lean/REVIEW.md),
with transparent AI-agent scope, and the Schiffer/Forsythe organization and
kernel-trust examples. No human review, official Tau Ceti endorsement or new
priority is claimed.

Before any implementation, both referees must approve the exact frozen
Definitions, Challenge and numerical targets. After implementation, each
advertised theorem needs fresh kernel and axiom checks, two independent final
reviews, actual Linux sandboxed Comparator/default-kernel replay and controls,
independent operational audit and publication review. Only then may a separate
problem PR promote the canonical entry to Lean verified. No commit, push or
publication is part of this statement-stage handoff.
