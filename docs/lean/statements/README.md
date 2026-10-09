# Complete problem statements in Lean

This campaign began at published commit
`80c0e3e638b2f26dcb3a00353651fc3d2215dd65`; the inventory records its current
published baseline. It preserves the permanent registry and the complete
canonical problem pages. It adds statements for solved, partially resolved,
and open targets without changing their mathematical status.

The [coverage register](COVERAGE.md) inventories all registered IDs and
separates source existence from mathematical completeness. Historical source
copies and review artifacts do not count as active Lean statements. Existing
external statements keep their original credit. Existing local scaffolds
with missing semantics or subquestions remain explicit coverage gaps.

## Review before implementation

For each ID, retain the entire canonical README byte for byte as
`ORIGINAL.md`, together with its canonical path, published revision and
SHA-256 hash. Write `NUMERICAL_TARGETS.md` before Lean code. It must describe
every subquestion, quantifier, field, dimension, norm, probability law,
numerical constant, endpoint and computational model. A complexity question
requires a genuine cost model and admissible algorithms; an arbitrary
function called a cost does not supply one. A request to determine an exact
value cannot be replaced by the existence of a maximum.

Obtain two independent specification reviews, recording the exact source and
specification hashes. Correct substantive findings before implementation.
After implementing the proposition, obtain two independent boundary reviews
of the actual definitions, imported semantics and frozen source. AI-agent
reviews are labeled as such. Authors do not count as their own referees.
Changing mathematical source bytes reopens the corresponding review gate.

## Statement library and checking

The shared [Lean package](../../../lean-statements/README.md) pins Lean,
Mathlib and LeanCert. Targets are explicit `Prop` definitions with no
placeholder semantics or target axioms. They assert no proof of the problem.
The separate statement workflow checks elaboration, permitted axioms,
metadata, review hashes and equality to the frozen reviewed statement.
Comparator equality certificates establish correspondence of statements,
not the truth of an open or solved target. The existing proof-verification
workflow and its promotion requirements remain unchanged.

Numerical proof certificates must use LeanCert kernel trust, both the
global option and explicit tactic setting, and pass a transitive trust
audit. Prefer exact algebra and proved reductions; no interval calculation
is required just to define a proposition. The infrastructure smoke test is
not a theorem about any catalog problem.

## Working order and evidence

Work through solved targets, then partially resolved and open targets,
grouping reusable mathematical definitions only after their exact meaning
has been reviewed. Specification-ready and model-incomplete drafts remain
visible, but do not count as completed formal statements. Local macOS
elaboration and Linux isolated Comparator evidence are recorded separately.
Neither historical logs nor a configured CI workflow imply a fresh passing
run.
