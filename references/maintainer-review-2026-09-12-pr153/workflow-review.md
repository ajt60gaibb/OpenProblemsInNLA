# PR153 workflow, selection, and metadata review

Original exact head: `eaf3b80698555171804bef29e3a9e2b1607bc875`, inspected in
`/private/tmp/nla-pr153`. Reviewer: independent Codex agent `/root/audit_trace`.
Scope: `.github/workflows/lean-verification.yml`, `tools/lean/projects.py`,
`tools/lean/validate_manifest.py`, pinned metadata schema, and
`tests/test_lean_verification.py`. Harness/kernel execution and archived Linux
operational evidence have separate reviewers.

**Original-head verdict: FAIL because two affected-project selection cases
silently skip required verification.** Both were independently reproduced in
scratch Git repositories before edits. Root subsequently authorized this
reviewer to repair the selector, the inline shared-tool detector, and their
tests. The repaired source passes the local checks described below; root owns
the independent review of my implementation and the fresh CI run. This report
does not retroactively approve the original head or present my repair review
as independent of its author.

## Reproduced findings and repairs

1. **Complete project deletion or rename disappears from selection.** Original
   `projects.py:20–23,45` discovers only directories remaining in HEAD. Removing
   all of a registered `ID/lean/` directory, or renaming it to `lean-archive/`,
   returns exit 0 with `{"include":[]}`, even while the original registered
   README still says `Lean verified`. The subsequent workflow skips `verify`
   at line 95. Partial file deletion is selected correctly; the failure is the
   complete-directory case. The permanent-ID checks do not require retaining
   the Lean directory, so preserving the README/registry alone does not catch
   this omission.

   Repair: discover registered project presence in both the base Git tree and
   current tree; reject missing base projects before emitting a matrix/count.
   A moved/deleted project cannot silently become a successful zero-project
   run. Surviving projects and newly added source-only projects retain the
   existing selection behavior.

2. **Git's quoted pathname output hides changed proof/tool files.** Original
   `projects.py:47–50` uses text `git diff --name-only` followed by
   `splitlines()`. Git quotes a valid Unicode dependency path such as
   `linear/IE-19/lean/Δ.lean`; the resulting string starts with a double quote,
   so the project-prefix predicate misses it. An otherwise ordinary change to
   that dependency returned exit 0 with an empty matrix. Quote-containing
   filenames reproduce the same issue. Newline-containing paths are another
   case where line-oriented parsing cannot preserve Git filenames. The inline
   `tools_changed` detector at workflow line 42 had the same quoting issue and
   additionally allowed rename detection to hide a tool's old location.

   Repair: both Git diff consumers use `--no-renames -z` and split at NUL,
   preserving every filename and both ends of a move. New regressions execute
   the actual workflow's inline Python detector, not a copied approximation.

Original evidence: `pr153-selection-probes.py` and
`pr153-selection-probes.json`. The old JSON is deliberately retained unchanged
and records the vulnerable selector's SHA-256. Its 11 scratch cases also
confirm normal proof changes, partial deletion, ordinary shared changes, and
source-only additions select the expected projects.

## Repaired selection tests

Ran the pinned dependency environment after all repairs:

```text
/private/tmp/nla-pr153-venv/bin/python -m unittest discover -s tests -p test_lean_verification.py -v
Ran 30 tests: OK
```

The original 20 cases remain. New Git-backed tests cover complete deletion;
rename away; partial deletion; a file moved between two surviving projects;
source-only addition for an existing registered ID; Unicode, quoted, and
newline proof paths; the same shared-tool filenames; and a shared tool renamed
outside its original directory. The workflow detector is extracted from the
parsed workflow and executed against real base/head Git fixtures.

The shared-control/project distinction is unchanged and explicitly tested:
`docs/lean/ci-toolchain/` affects the standalone control fixture and requests
`checker-controls`, but does not rebuild problem projects. Those projects use
their own toolchain pins, while changes to the actual shared verifier lock or
implementation under `tools/lean/` select every project. Schema/workflow and
registry changes continue to select all registered current projects.

`git diff --check` passes for all three edited files. No commits, pushes, or
public comments were made by this reviewer.

## Metadata and path-containment assessment

The pinned schema is the permissive upstream v0.4 metadata standard, not a
proof verifier. The primary immutable source was read at
<https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json>.
The local schema SHA-256 is
`25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce`.

`validate_manifest.py` selects the schema's declared JSON-schema dialect,
checks the schema itself, rejects duplicate YAML/JSON keys, requires explicit
v0.4 and zero reported proof-development sorries, and requires exact set/count
agreement between advertised results and selected comparator theorems. It
rejects definition holes and custom/native axioms and requires each result to
refer to the checked `comparator.json`. Resolving each source file before
checking containment correctly catches parent traversal, absolute external
paths, and symlink escapes.

Independent additional probes passed 11/11 expectations: valid metadata;
parent traversal; absolute external source; symlink escape; absent source;
Boolean false masquerading as integer zero; absent completed status; duplicate
result declaration; comparator/result mismatch; wrong comparator reference;
and a custom result axiom. Evidence is `pr153-manifest-probes.py` and `.json`.
No candidate Lean code or dependency setup was executed by these probes.

This validator intentionally checks consistency of self-reports. It does not
prove source attribution, actual reported axiom lists, source-file declaration
ownership, informal theorem fidelity, or the truth of referee reports.
`review.status=unchecked` is accepted by the schema. The docs' independent
referee/promotion requirements therefore remain separate gates. The harness
also performs stricter comparator-config type/key validation, so incomplete or
malformed configs cannot become a successful end-to-end proof merely because
the metadata-only validator accepts them.

Discovery's lexical relative-path guard rejects absolute paths and `..`;
the permanent-ID validator separately enforces exact canonical category/ID
paths, duplicate-free registration, retained IDs, and non-symlink canonical
ancestors. Discovery rejects a symlink as the project directory, and the
harness's `regular_path` plus tracked-file snapshot rejects symlink ancestors
and project contents before its fresh verification. No end-to-end escape
through a result-file alias was identified in this scope.

## Workflow permissions, trust, and failure propagation

The workflow uses ordinary `pull_request`, `push`, and manual-dispatch events;
read-only repository permissions; exact action revisions; no retained checkout
credentials; and environment variables with quoted shell arguments for
project paths. No secrets or `pull_request_target` privileged checkout pattern
is present. The select checkout fetches full history for base comparisons.

Executed validation/control/verification commands fail their jobs on nonzero
exit; there is no `continue-on-error`. Matrix `fail-fast: false` lets other
projects finish without masking a failure. The always-running artifact step
retains logs and does not reset failed verification to success.

There is no final, stable aggregate job: failed `select` causes dependent jobs
to skip. Branch protection must therefore not require only an optional
`verify` job while omitting `select`/applicable checker-controls. GitHub documents
that skipped jobs are treated as successful required checks:
<https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/control-jobs-with-conditions>.
I did not inspect remote branch-protection configuration; this is a deployment
configuration limit, not a demonstrated all-jobs-green bypass after the fixes.
The coordinating maintainer reports that the permanent-ID check is currently
required and will additionally require successful `select` and
`checker-controls` before merging this infrastructure PR. That manual merge
gate addresses the immediate integration; it is not a claim that this workflow
installs an aggregate required-check rule.

The workflow consumes the reviewed PR checkout's infrastructure, Challenge,
Lakefile, dependency pins, and comparator configuration. It does not fetch a
separate base-revision challenge or enforce frozen referee hashes. As expressly
documented in `HARNESS.md`, those inputs are separately trusted; only candidate
Solution compilation/export is subject to the proof sandbox. Semantic review
must establish that the trusted boundary still matches the original canonical
target. A changed challenge that becomes easier is not detectable by comparing
it with a correspondingly changed proof alone. This is an explicit trust-model
limit, not a claim that the kernel verifies English-to-Lean correspondence.

Fresh Linux execution of the repaired workflow remains required. The retained
operational archive proves what ran at its own older immutable revision, not
these subsequently repaired selector/workflow bytes.

## Repaired-file identities

Working-tree hashes after the tests, based on original head `eaf3b806`:

| File | SHA-256 |
| --- | --- |
| `.github/workflows/lean-verification.yml` | `2c3963089483ec5e7e35e6355fa60988778e0b439ce099d7cd7050a8c3b6467c` |
| `tools/lean/projects.py` | `dbb8e2df074d2518c4457ff66229891161104767381762fbd5f96d7f28dee149` |
| `tools/lean/validate_manifest.py` (unchanged) | `31e473132c1e8a40c29f73eff01fbff0bafe85649da601d2f550cef164debeb1` |
| `tests/test_lean_verification.py` | `b7e5309eaa6518fd09757a144a5a486321336e744b520e6c89b9c1a327f81757` |

No additional merge blocker was identified in the assigned metadata/selection
scope after the repairs. This excludes independent approval of my own patch,
remote required-check configuration, full Linux harness validation, and
mathematical correctness of future registered projects.
