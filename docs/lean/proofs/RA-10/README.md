# RA-10 completed proof: verification guide

The full proof establishes the unchanged `NLA.Statements.RA10.Target` with
universal constant 11. Its substantive sources are pinned to commit
`844237f7e979146c937c0dc88f5c3f6e5f40c9b9` in the
[isolated RA-10 proof project](../../../../randomized-and-low-rank-approximation/RA-10/lean/README.md).
Two independent AI-agent final source reviews and isolated non-root Linux
Comparator/LeanCert kernel verification are complete; the
[receipt](LINUX_CI_RECEIPT.md) binds the checked source bytes.

## Start here

- [Final theorem](../../../../lean-statements/NLA/Proofs/RA10/OperatorMonotoneRepresentation.lean):
  `NLA.Proofs.RA10.ra10_target`, via `transferBound_eleven` and the unconditional
  representing-measure theorem.
- [First final source review](../../../../randomized-and-low-rank-approximation/RA-10/lean/reviews/FINAL_FORMALIZATION_REVIEW_1.md)
  and [second final source review](../../../../randomized-and-low-rank-approximation/RA-10/lean/reviews/FINAL_FORMALIZATION_REVIEW_2.md): exact target, source hashes, and full proof path.
- [Isolated Linux receipt](LINUX_CI_RECEIPT.md): Comparator acceptance,
  LeanCert kernel trust, and exact artifact hashes.
- [Completion checklist](COMPLETION_CHECKLIST.md): proof sections, reuse and
  completed verification gates.
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
implementation was developed with OpenAI Codex assistance. The isolated wrapper
uses pinned Mathlib and LeanCert dependencies.

## Reproduce the local check

From `lean-statements/`, with the committed dependency pins:

```bash
lake exe cache get
lake build NLA.Proofs.RA10.OperatorMonotoneRepresentation NLA.Proofs.RA10.OperatorMonotoneConcavity
shasum -a 256 -c ../docs/lean/proofs/RA-10/verification/2026-10-11-upstream-pr/source-sha256.txt
```

The final representation, transfer and target report only `propext`,
`Classical.choice` and `Quot.sound`. The source build is retained as historical
evidence; the [isolated project](../../../../randomized-and-low-rank-approximation/RA-10/lean/README.md)
and [Linux receipt](LINUX_CI_RECEIPT.md) provide proof-target Comparator
verification.

## Historical upstream review scope

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

The canonical mathematical target and permanent ID are unchanged. The
[canonical page](../../../../randomized-and-low-rank-approximation/RA-10/README.md)
retains the complete original question and records the completed reviews and
proof-target verification. Older hash-bound reviews and partial build logs
remain historical development evidence.
