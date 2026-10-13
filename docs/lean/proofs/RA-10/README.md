# RA-10 completed proof: review guide

The candidate proves the unchanged `NLA.Statements.RA10.Target` with universal
constant 11. The upstream submission extends the RA-10 foundations in
[PR #350](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/350) at
`696b59ff414c74d24bfef71ab22e6d67b5c0f7cd`.
Local Lean checking is complete; independent review and isolated non-root
Linux Comparator verification remain outstanding.

## Start here

- [Final theorem](../../../../lean-statements/NLA/Proofs/RA10/OperatorMonotoneRepresentation.lean):
  `NLA.Proofs.RA10.ra10_target`, via `transferBound_eleven` and the unconditional
  representing-measure theorem.
- [Completion checklist](COMPLETION_CHECKLIST.md): proof sections, reuse and
  the remaining verification gates.
- [Ridge transfer](SPECTRAL_TRANSFER_PROGRESS.md): compression, spectral
  perturbation and constant-11 assembly.
- [Operator-monotone representation](REPRESENTATION_PROGRESS.md): compactness,
  harmonic extreme points, Hansen splitting, Bendat–Sherman and measure existence.
- [Upstream submission evidence](verification/2026-10-11-upstream-pr/README.md):
  local build, transitive axiom reports and the manifest of 104 source hashes.
- [Original completion evidence](verification/2026-10-11-complete/README.md):
  the earlier local check on the aggregate proof-development baseline.

The mathematical source is George Stepaniants's
[RA-10 solution](../../../../randomized-and-low-rank-approximation/RA-10/solution.md),
Theorem 1, Lemma 2 and Sections 3–5. The representation development follows
the route discussed in [the representation note](REPRESENTATION_PROGRESS.md#reuse-audit),
using Mathlib's Krein–Milman, measure compactness and integration APIs. This
implementation was developed with OpenAI Codex assistance and adds no external
library dependency.

## Reproduce the local check

From `lean-statements/`, with the committed dependency pins:

```bash
lake exe cache get
lake build NLA.Proofs.RA10.OperatorMonotoneRepresentation NLA.Proofs.RA10.OperatorMonotoneConcavity
shasum -a 256 -c ../docs/lean/proofs/RA-10/verification/2026-10-11-upstream-pr/source-sha256.txt
```

The final representation, transfer and target report only `propext`,
`Classical.choice` and `Quot.sound`. The final build passed again during PR
preparation. A separate CI step builds these candidate modules without adding
them to the reviewed proof aggregate. That build is not the independent
Comparator verification of the target; existing statement-identity checks do
not verify the target's truth.

## Upstream review scope

The draft PR is submitted from
`FormulaRabbit81:codex/ra10-complete-upstream` to upstream's
`codex/nla-proof-ra10` branch. It depends on PR #350, which supplies the
existing RA-10 foundations and is itself based on the shared proof
infrastructure in PR #344. The new PR contains the completion work, rather
than the unrelated problems from the former aggregate PR #342.

The earlier [fork review PR](https://github.com/FormulaRabbit81/OpenProblemsInNLA/pull/2)
is retained. Its 97 proof sources are unchanged in this submission. The
dedicated upstream RA-10 base supplies two additional existing modules,
giving 99 RA-10 proof files in this tree; neither is a new dependency of the
final representation theorem.

The canonical problem, mathematical target, dependency pins and catalogue
status are unchanged. Before claiming the repository's `Lean verified`
status, the final source requires independent reviews and the proof-target
Comparator setup and isolated Linux verification described in the
[per-problem workflow](../../README.md). Older hash-bound reviews and partial
build logs remain historical evidence; they do not review these new sources.
