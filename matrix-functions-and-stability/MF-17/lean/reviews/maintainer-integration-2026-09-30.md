# MF-17 maintainer integration review

Date: 30 September 2026. Reviewed submission: [PR #325](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/325),
commit `cad3785440a2678b5b30aa8133d425e709b6811d`.

## Scope and verdict

Three independent Codex AI agents reviewed the submitted sources and retained
verification evidence. They found no blocking defect within their inspected
scopes. These are informal AI reviews, not external human peer review. The
maintainer integration did not rerun Lean or the Linux Comparator; it reviewed
the actual retained run and checked its source correspondence.

- `mf17_statement_review`: approved statement fidelity and non-vacuity. The
  original problem statement is byte-identical to the published base. Actual
  definitions use the full strong generator graph, the operator exponential,
  and arbitrary complete complex Hilbert spaces. The five contracts cover
  inverse existence, finite envelope, fixed-M sharp growth, finite-dimensional
  lower witnesses with the same M, and the M=1 endpoint. The reviewer also
  inspected manuscript Part VI, Theorem S.1.1, printed page 42 / PDF page 43.
- `citation_scope`: found no blocker in the principal upper, lower and endpoint
  proof paths. The upper proof includes the exact kernel representation and
  strong-limit bridge. The lower proof supplies its concrete boundary family,
  preserves M through the finite-dimensional construction, and reaches every
  sufficiently large time by rescaling. The scalar construction and refined
  constants are accurately disclosed in `NUMERICAL_TARGETS.md`.
- `mf17_evidence_review`: approved the retained mechanical evidence and its
  binding to the published source, subject to the publication correction below.
  Separate Challenge/Solution builds, all five comparisons, permitted axioms,
  default-kernel acceptance, real sandbox controls, rejection controls and
  overall harness exit 0 are recorded in the retained logs. The documented
  storage and process-throttling accommodations do not alter proof inputs or
  the checker. Solution's import closure excludes Challenge.

The source reviews cover the mathematical boundary and selected major proof
paths, not a line-by-line informal reproof of every analytic lemma. No local
pinned Mathlib checkout was available for an exhaustive reuse audit.

## Receipt binding and publication correction

The unchanged [successful receipt](../verification/linux-verification/result.json)
records the submitter's local commit
`ac582d01532a914538cbfb74863437b18433038a`. That commit was not included in the
published PR history; its original GitHub link returned no commit. The public
source link now identifies the actual published submission commit `cad37854`.

Every one of the 224 Lean files matches the corresponding SHA-256 value in
the receipt: 220 `ProofProject` modules, `Solution.lean`, `Challenge.lean`, and
the two verification scripts. The dependency pins, `lakefile.toml`,
`comparator.json`, `NUMERICAL_TARGETS.md`, and all three submitted reviewer
reports also match. No unrecorded Lean source or build/configuration input was
found. Among the receipt's 246 input files, only the project's README,
`formalization.yaml`, and verification README differed at the published
submission; those differences concern documentation and evidence metadata.
The checker source-lock hash and bootstrap tool receipt also agree.

The integration preserves all proof sources, statement contracts, dependency
pins, original reviewer reports, runtime logs, successful receipt, and submitted
manuscript. It corrects the public source link and stale draft wording, records
the distinction between the local run and published snapshot, and resolves
generated catalog conflicts against current main. This report is new review
evidence and was not an input to the earlier Linux run.

Selected SHA-256 values:

```text
Definitions.lean      d6ca7cb8cd5ab8ffba64ad903c55e2153bb505d298616d6d1bac97e68767204a
Challenge.lean        b8a14a878b4a8aced61b0de4f8f5d90b2c488e9d5c63a7748a9a84092982b4d6
Solution.lean         cea58f6ca9fa54d0a8951e356f38d42f51e95ff6bdb101039e94303c91d7567c
NUMERICAL_TARGETS.md  8404a7ca5da860ba7298fcf540a69887c74e0da3fce469949885428d5ea83bc3
manuscript PDF       40bb30b1d087625d0b434d34ce8380d96081095c840ce6bd1f95cea9d280dec4
```

## Integration validation

- All 217 permanent IDs passed validation against `origin/main`; all 17
  permanent-number safeguard tests passed.
- All 84 repository unit tests and 12 Lean-harness unit tests passed, including
  the Pandoc mathematics-conversion tests.
- The formalization schema and exact five-declaration Comparator coverage
  passed. GitHub mathematics formatting and integration-diff whitespace checks
  passed. The submitted runtime logs retain their original whitespace.
- Catalogs and the statement inventory were regenerated, preserving the
  inventory's existing published base. The inventory now recognizes MF-17's
  live formalization and Lean-verified status.
- The canonical problem TeX/PDF were regenerated with the repository renderer.
  The final build reported no layout warnings; all three PDF pages were
  visually inspected.

These checks validate integration and metadata. They do not represent a new
execution of the mathematical Lean proof or its isolated Linux verification.
