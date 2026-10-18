# SP-11 canonical packaging and acceptance plan

Prepared by `/root/solved_inventory`, 18 October 2026. This is a concrete package
plan and boundary record, not a certificate that the target proof is complete.

## Present frozen boundary

The canonical package is `eigenvalues-and-inverse-problems/SP-11/lean/`.
`NLA/Statements/{Infrastructure,SP11}.lean` are byte-identical copies of the shared
live reviewed sources. `Reviewed/SP11.lean` is the separately frozen reviewed
source. `Identity.lean` proves equality of the live and frozen Target propositions
by `rfl`, with LeanCert kernel trust. `ORIGINAL.md` is an exact copy of the original
canonical page, and `NUMERICAL_TARGETS.md` is copied without historical edits.
The source hashes and copy origins are in the package's
`boundary-source-lock.json`.

The exact Challenge export is frozen before implementation:

```lean
import NLA.Statements.SP11
set_option autoImplicit false
namespace NLA.SP11
theorem target : NLA.Statements.SP11.Target := by
  sorry
end NLA.SP11
```

That single sorry is the deliberate trusted Comparator challenge hole. The
package has no Solution.lean and no asserted proof of Target. The selected future
export is exactly `NLA.SP11.target`; `comparator.json` selects no definition holes
and allows only `propext`, `Classical.choice`, and `Quot.sound`.

The target is every natural n>0 and every finite simple graph on Fin n, a real
square matrix symmetric on all entries, off-diagonal nonzero iff adjacency, and
minimum degree <= n minus natural matrix rank. Diagonals and edge signs are free;
isolated vertices, disconnected graphs and n=1 remain included. There is no PSD,
SAP, connectivity, positive-minimum-degree or regularity premise. Matrix
rank-nullity gives the exact nullity convention. No alternate theorem or
conditional uniqueness assumption may replace this export.

## Finish the self-contained package

After the full proof closes and this boundary receives two independent
hash-bound approvals, copy the final closed import graph from
`lean-statements/NLA/Proofs/SP11/` into the same package's `NLA/Proofs/SP11/`.
Copy ordinary source bytes only; do not include .lake, compiled objects, symlinks,
path dependencies, or dependence on an unmerged moving development branch.
Record the exact import closure and both source/destination hashes. Reviewers
must assess the final proof closure, not only the currently approved partial
support modules.

Write `Solution.lean` only after the final source theorem is available. It must
import that actual final module, export `NLA.SP11.target` with the exact copied
`NLA.Statements.SP11.Target` type, use `set_option leancert.trust "kernel"`, and
have no remaining hypotheses, sorry, axiom or assumed noncancellation lemma.
Run `#assert_trust kernel target` and `#print axioms target`. The actual final
source theorem/module name remains pending; this plan invents no completed
`NLA.Proofs.SP11.target` declaration.

Change lakefile defaultTargets to `["Solution", "Identity"]` and add the
Solution lean_lib. Keep Challenge available for Comparator. The current NLA
library already includes `NLA.Statements.+` and `NLA.Proofs.SP11.+`, with
separate Reviewed, Challenge and Identity libraries. Final package layout:

```
lean-toolchain, lakefile.toml, lake-manifest.json, LICENSE
formalization.yaml, comparator.json, README.md, NUMERICAL_TARGETS.md, ORIGINAL.md
Challenge.lean, Identity.lean, Solution.lean
NLA/Statements/{Infrastructure,SP11}.lean
Reviewed/SP11.lean
NLA/Proofs/SP11/<exact closed source import graph>
boundary-source-lock.json, reviews/, verification/
```

The toolchain is exactly `leanprover/lean4:v4.33.1`; direct dependencies are
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. The manifest is copied from the already
pinned RA-06 package and changes only its root name to NLASP11; all ten dependency
revisions stay fixed. The human-readable inherited inputRev branch names are
resolved by their manifest's immutable 40-hex revs. No path dependencies or
floating direct revs are introduced.

The custom boundary source lock is a review aid. Generic verification hashes the
committed project inputs independently; no existing SP-11-specific validator
enforces this custom lock. Do not claim otherwise or weaken the general harness.

## Metadata and project discovery

The current v0.4 metadata explicitly records a boundary-only phase,
`whole_problem_verified: false`, retained canonical status Solved, and zero
completed main results. Its zero proof-development sorry count excludes the
intentional Challenge placeholder, as prescribed by the pinned metadata schema.
The target proof file is absent; planned_results describes a plan only.

Consequently `tools/lean/validate_manifest.py` is expected to reject this
intermediate package because completed-project result coverage does not yet
match the selected future export. This is correct. Do not assert a fabricated
completed main result or bypass selection. `tools/lean/projects.py` discovers
registered canonical lean directories even if they are only drafts; after the
scaffold is committed, SP-11 will be selected on the relevant diff.

When Solution is complete, main_results must contain exactly one record,
`NLA.SP11.target`, file Solution.lean, sorry_count 0, the permitted standard axioms,
and comparator_config comparator.json. Report completed proof status truthfully;
keep whole_problem_verified false until the actual final Linux receipt and
independent final scope review warrant promotion. Credit Hall for the mathematical
theorem, Stepaniants for the application note, and AI agents for formalization.
There is no human peer-review or source-author participation claim.

## Reproducible checks and authoritative receipt

Run at repository root after final integration:

```bash
python3 tools/lean/validate_manifest.py eigenvalues-and-inverse-problems/SP-11/lean
python3 tools/lean/projects.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_lean_verification.py' -v
```

Run `lake build Challenge Identity Solution` inside the canonical package after
materializing its pinned dependencies. Audit the exact selected Target export
and its complete axiom closure. Local macOS build output is supporting evidence;
it is not Linux Comparator acceptance. The boundary's current fresh isolated
local check is in `boundary-scaffold-evidence-2026-10-18/` and intentionally
contains no Solution theorem.

Use the existing `.github/workflows/lean-verification.yml` without a weaker
SP-11 profile. A non-root Linux invocation, with tools outside the project, is:

```bash
tools/lean/bootstrap.sh /absolute/outside/projects/nla-lean-tools
tools/lean/selftest.sh /absolute/outside/projects/nla-lean-tools
tools/lean/verify.sh eigenvalues-and-inverse-problems/SP-11/lean /absolute/outside/projects/nla-lean-tools
```

The default profile suffices. The real verifier requires a committed unchanged
self-contained project at HEAD, pinned ordinary source files, a non-root Linux
process with the sandbox/user namespace setup, Go, the pinned Lean toolchain,
C compiler, Python and git. The current workflow supplies Ubuntu 24.04, Go
1.27.1, bubblewrap, user D-Bus/systemd and the required user namespace setup.
Bootstrap and verifier run the real sandbox, raw-kernel and Comparator controls,
including negative controls; acceptance must not be simulated from local builds.
The verifier independently snapshots committed inputs, materializes dependency
sources, runs the actual Comparator, then generates its own ProofTrustAudit.lean
for the selected theorem using the pinned LeanCert kernel check. Do not commit a
reserved ProofTrustAudit.lean file.

Retain actual result.json, comparator.log, leancert-proof-trust.log,
leancert-build.log, controls and immutable input/tool hashes from the verify log
directory, and link the Linux CI job/artifact `lean-SP-11` at the final commit.
The useful final state is real Comparator acceptance plus kernel-checked proof
trust for `NLA.SP11.target`, not merely a green support-only CI job. Two
independent reviewers must examine that exact final source closure and unchanged
original target. Then and only then may the canonical page link the verified
proof and update status with its receipt.

If canonical pages/indexes are changed at final promotion, keep the permanent ID
and canonical path untouched and run the required publication checks:

```bash
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
```

No original mathematical target, original page snapshot, canonical TeX/PDF,
registry identity, historical source credit, or other problem is changed by the
current scaffold.
