# IE-06 publication authorization — 2026-10-06

The maintainer reported: “I have permission from John Urschel now to push this
to the github repo.” This authorizes publication of the prepared IE-06 proof
package. It records the maintainer's report of publication permission; it does
not claim that Urschel reviewed the Lean source, certified its correctness,
or endorsed the AI-agent reviews. No agent contacted him or sent correspondence.

## Immutable proof and retained evidence

The complete, previously delivered package is committed without source changes
at [263a215acd295a260dec7a75ff6bebebb9789df9](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/263a215acd295a260dec7a75ff6bebebb9789df9/linear-systems-and-elimination/IE-06/lean).
It was copied from the verified delivery manifest into a clean worktree based
on main at `a345cfc7`, on branch `codex/ie06-probabilistic-proof`.
All 121 final-validation inputs, including all 114 Lean modules, retain their
accepted hashes. Subsequent publication edits concern documentation, source
metadata, the canonical evidence links, generated documents, and the delivery
inventory. The original working checkout and its preexisting edits are retained.

[The successful local record](verification/SUMMARY.md) covers fresh compilation,
3,229 owned-declaration axiom checks, six actual Comparator comparisons, and
rejection controls. The authoritative Linux sandbox, exporter, and independent
raw-kernel replay were not run in that historical local record. They subsequently
passed in the authoritative Linux CI run below; publication alone was not the
evidence for that result.

All original execution receipts and dated reviews describe the source and
publication state at their own recorded time. In particular, historical
“not pushed”, “not contacted”, and initial statement-only tooling-lock scope
labels are historical, not the current publication status. The unchanged
prepublication inventory is retained as
[prepublication-delivery-manifest.json](verification/prepublication-delivery-manifest.json).
The retained [delivery manifest](verification/delivery-manifest.json) records
that publication snapshot. It is not rewritten to include the later CI evidence
or current status-document updates. No proof hash or old execution result is
rewritten.

## Subsequent authoritative Linux verification

[GitHub Actions run 37513136002](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/37513136002), job
[112439363988](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/37513136002/job/112439363988), passed the full IE-06
Comparator verification for PR head `05b1c83e11042d7067cd51c5a4bfc0265e7390f4`.
The executed pull-request merge commit recorded by the harness is
`6091e87aa8538ea31df21fd06cce3d9e42f65c2a`. The package was subsequently
merged; the promotion checkout was `6ea93e3194bed8b2e65b846573ddafbfd6b66eff`.

The [retained evidence](verification/linux-ci-2026-10-06/README.md) includes
the complete small CI artifact, its provenance, all six actual exported targets,
strict sandbox probes, exporter execution, accepted default-kernel replay, and
rejection controls. Its original result SHA-256 is
`e8d6ccc4501c435ca30d48bb8b9940ce6bcba9417b884b9625f4414ef102f168`.
All 1,139 receipt-listed inputs matched the promotion checkout before edits.
The present promotion changes status documentation/metadata and adds evidence;
the audited Lean proof inputs and historical receipts remain unchanged.
CI acceptance does not imply human peer review or Urschel's correctness endorsement.

## Source attribution

The mathematical proof is credited to Urschel and the original conjecture to
Trefethen, including its presentation with Bau. Other credited sources and
licenses remain as recorded. The metadata uses `author_endorsement: other` only
for Urschel, with the publication-permission distinction above.

The local Gaussian-null, smallest-singular-value, and regression adaptations
retain their RRF source paths and hashes in `source/gaussian-*-provenance.json`.
Those historical records described local use pending publication review.
The maintainer's authorization applies to publication of this prepared package,
including these reviewed adaptations. No separate upstream license notice was
found in those individual local source files; this record does not invent an
Apache release or imply that Urschel authored or licensed that RRF source.
The isoperimetric and SLT adopted proofs retain their separate Apache licenses,
immutable upstream revisions, and attribution. The generic IE-04 definitions
retain the recorded Stepaniants credit.
