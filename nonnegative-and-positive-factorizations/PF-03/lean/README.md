# PF-03: rational factors on the completely positive boundary

**The complete original target is Lean verified.**
Local serial Lean, two independent nonauthor source reviews and two actual
published-source Linux Comparator/kernel/sandbox runs pass. See [STATE.json](STATE.json)
and [formalization.yaml](formalization.yaml).

The formalized result is the complete negative answer to the retained
[PF-03 question](../README.md): some rational symmetric completely positive
boundary matrix of order at least five has no nonnegative rational Gram factor
of any positive finite width. Boundary is taken in the real symmetric-matrix
space. The final declarations are
`NLA.PF03.pf03_counterexample` and `NLA.PF03.canonical_negative_answer`.

Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons
Foundation, retains the original mathematical and exact seed-data authorship.
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, contributes formalization and proof
engineering with substantial Codex assistance. Source credits remain in the
component files. No external human peer review or source-author endorsement
of the formalization is claimed.

## Project and scope

`Solution.lean` imports only the implementation and requests axiom and
kernel-trust checks for all 25 frozen contracts. It is the default Lake target.
`Challenge.lean` is a separate trusted reference environment with 25 deliberate
proof placeholders; it is never imported by the solution. The byte-identical
frozen `comparator.json` compares all 25 declarations, allows only the three
standard foundational axioms and has no replaceable definitions.

The [implementation map](IMPLEMENTATION-MAP.json) identifies every contract.
The [numerical plan](NUMERICAL_TARGETS.md), frozen definitions and Challenge
retain their reviewed historical bytes, including draft-status comments;
current status is in STATE.json. The statement gate was approved by two
agents before proof implementation. Those agents later authored proofs, so
two different nonauthors conducted the final proof reviews.

The implementation replaces facet enumeration and the explicit order-444
matrix expansion with a proved rational Fourier–Motzkin halfspace
representation and five zero-row padding. This proves the same original
universal assertion false. The source's additional explicit-order,
strict-entry-positivity and minimal real cp-rank claims are outside this scope.

Only three fixed root-endpoint inequalities use kernel-mode LeanCert. Exact
cubic arithmetic, symmetry and a checked reusable QG product keep the other
certificates small. Cone geometry, unrestricted factor width and the boundary
argument are symbolic. No narrowed interval domain or unproved certificate
premise is introduced.

## Reproduction and evidence

The project pins Lean 4.33.1, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` in the committed Lake files.
From this directory, the standard local reproduction command is `lake build Solution`.
The recorded macOS development checks used direct serial Lean commands, not a
standalone Lake build; the Linux Comparator logs separately record fresh
Challenge and Solution builds. The campaign uses
one serial local compiler process, one thread and a 4096 MiB limit, with
source-matched pinned dependency outputs.

The [actual local audit](verification/local-2026-09-19/LOCAL-REPLAY-AUDIT.json)
authenticates the 59 implementation modules, their original successful commands,
and the fresh Solution aggregate in recovery-047. It retains lossless original
receipts and checks every reused source, transitive source, log and output hash.
The [aggregate log](verification/local-2026-09-19/logs/recovery-047/Solution.log)
reports only the three standard foundational axioms for all 25 contracts;
all 25 kernel-trust assertions passed. This is a macOS local check, not the
Linux Comparator/sandbox check. The [packaging snapshot](PACKAGING-SOURCE-SNAPSHOT.json)
is a separate earlier source-copy observation, not another compiler run.
The independent final reviews are [referee 2](reviews/final-referee2/REVIEW.md)
and [referee 3](reviews/final-referee3/REVIEW.md). A
[supplementary review](reviews/final-referee1/REVIEW.md) by an earlier definitions
author is retained separately and excluded from the two-reviewer independence
count. These AI-agent reviews inspected source and actual local evidence; they
did not rerun Lean or Comparator. The separate Linux executions are recorded below.

Final review applies the repository's pinned Tau Ceti guidance manually. This
does not represent official Tau Ceti service execution. Local Lean checks and
GitHub Comparator checks are recorded separately. The [consolidation notes](PACKAGING-NEXT-STEPS.md)
are retained as a historical pre-publication checklist; STATE.json records the completed gates.

## Published Linux verification — 19 September 2026 (UTC)

The immutable proof commit is
[9625a76780183040186664100e24e0e90d8fcc7d](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/9625a76780183040186664100e24e0e90d8fcc7d/nonnegative-and-positive-factorizations/PF-03/lean).
The [fork push run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35424055075)
and [upstream PR run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35424087832)
both passed all 25 exact contracts. Each selected only PF-03 and checked all
234 published project input files against that revision. The upstream run
used GitHub's synthetic merge commit; its project files matched the proof
commit exactly. Both runs checked exported proof bodies with the default Lean
kernel and Comparator, allowed only the three standard axioms, and passed
the real sandbox and rejection controls. The separately skipped shared-checker
job did not skip these per-proof controls.

The [summary](verification/linux-2026-09-19/SUMMARY.json), original GitHub
artifact ZIPs, provenance, actual command logs and source hashes are retained.
The [root audit](verification/linux-2026-09-19/ROOT-AUDIT.json) and
[independent operational review](reviews/runtime-referee2/REVIEW.md) inspect
those executions; neither represents another compiler run. The copied original
audit script records its original recovery-directory layout, not a portable
replacement for the repository verifier.

For the full Linux check, follow the non-root isolation setup in the
[repository workflow](../../../.github/workflows/lean-verification.yml), then,
from the repository root, run the pinned bootstrap and verifier:

```sh
tools/lean/bootstrap.sh /tmp/pf03-lean-tools
tools/lean/verify.sh nonnegative-and-positive-factorizations/PF-03/lean /tmp/pf03-lean-tools
```

[Upstream pull request #303](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/303)
requests inclusion in main. This formalizes one previously solved original
target; it is not an additional mathematical resolution.
