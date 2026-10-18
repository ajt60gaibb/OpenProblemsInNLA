# Solved Lean proof campaign, 17 October 2026

**Active and incomplete.** The user requested exact Lean proofs of every Solved
problem without one, starting with FR-05, using independent agents and
LeanCert kernel mode. SP-11 is now promoted to Lean verified; permanent IDs
and original mathematical targets are unchanged.

The initial working checkout was stale and had unrelated uncommitted work.
The campaign uses published base `47006df8b3a6c724a557266c891893d03e69323a`
in a separate clone on `codex/solved-lean-campaign-oct17`. All 217 permanent
IDs, canonical pages, and original mathematical targets are preserved.

- **FR-05:** Already complete upstream. The [fresh statement review](fr05/fr05-statement-review.md)
  confirms the Gaussian/all-signals original limit and stronger inverse-dimension
  bound. The [artifact audit](verification/fr05-artifact-check.json) passes 33
  checks and matches every one of 154 historical project input hashes to current
  source. The FR-05 Linux job succeeded, although its larger multi-project
  workflow was cancelled. This audit reuses actual retained evidence; it is not
  a new Linux proof run.
- **Remaining queue:** The [independent registry inventory](inventory/README.md)
  records 42 Solved entries on published main, existing partial/full candidates,
  and later RA-10/MD-03/MD-04 evidence. Proof existence, complete-target scope,
  verification and canonical promotion are tracked separately.
- **SP-11:** Thirty-six completed [modules](../proofs/SP-11/README.md) establish
  greedy ordering and relabeling, the actual polynomial construction, exact
  signed-monomial expansion, classwise color recovery, diagonal and edge
  uniqueness, simultaneous real specialization and the rank reduction.
  `NLA.Proofs.SP11.target` proves the full unchanged frozen target. Independent
  AI-agent reviews, fresh local kernel/axiom audits and the
  [actual Linux Comparator/kernel receipt](../proofs/SP-11/LINUX_CI_RECEIPT.md)
  pass. The receipt binds all 135 project inputs at immutable commit
  `9264361fafb89b37b5c48236afebb304bc84110a`. The original page, TeX and PDF
  are archived byte for byte. The subsequent descriptive metadata refresh
  receives another committed-project CI check.

Reproduction scripts, raw logs, dependency/source hashes, rejection controls,
and the all-canonical preservation manifest are in [verification/](verification/).
Local checks use Lean 4.33.1, the pinned Mathlib and LeanCert revisions, and
read-only dependency caches with fresh output directories. The existing CI
aggregate imports the complete 36-module SP-11 proof closure. The seven-module
support receipt remains historical; the new dedicated full-project receipt
records actual SP-11 proof comparison. Shared statement identities remain a
separate check.

SP-12 is the next proof development, in a separate checkout, after two fresh
independent reviews of its exact PSD/SAP/chromatic statement. The other Solved
entries remain in the queue; this milestone does not complete the user’s
overall goal.
