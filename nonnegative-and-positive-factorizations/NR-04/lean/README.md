# NR-04: the nine-point distance matrix has nonnegative rank seven

Formalization by **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology**, with substantial Codex assistance. **Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge**, retains original mathematical authorship. The reflection construction retains the source's Hrubeš and Gillis–Glineur attribution.

The final theorems `NLA.NR04.nine_point_nonnegative_rank_seven` and `NLA.NR04.canonical_six_factor_impossible` settle the unchanged original target over arbitrary real nonnegative factors. The indexing theorem identifies Fin9 differences with the original labels 1 through 9. All widths are included in the lower bound, including zero and degenerate factor columns.

## Verification status

All 15 frozen contracts passed actual local serial Lean in recovery-086 and the publication-name aggregate in recovery-087. The [source and reuse audit](verification/local-2026-09-19/LOCAL-REPLAY-AUDIT.json) authenticates 41 proof modules, their actual commands, logs, output hashes and successful dependency-matched reuse origins. The coordinator allowed one compiler, one thread and 4096 MiB. The archive script itself ran no Lean. Only `propext`, `Classical.choice` and `Quot.sound` occur in the [actual transitive reports](verification/local-2026-09-19/actual-axioms.json).

Two wholly nonauthor AI-agent final source reviews passed: [referee A](reviews/final-referee-a/REPORT.md) and [referee B](reviews/final-referee-b/REPORT.md). The real published-source Linux Comparator/default-kernel/sandbox checks also passed, with a separate independent evidence audit. The complete original target is Lean verified. Historical frozen statement comments are retained as evidence of the pre-proof phase; `STATE.json` records the current phase.

## Proof structure and computation

An exact seven-column reflection factorization supplies the upper bound. The lower bound normalizes arbitrary factors, proves a geometric section contact bound, and applies a fully proved rank-nullity form of Sylvester's inequality to both factors. A separating affine key and a nine-grid crossing-parity obstruction prove the exceptional planar bound. The proof avoids enumeration of all point orderings and never substitutes a rational search for arbitrary real factors.

Kernel-mode LeanCert certifies the fixed inequality `0 < (8 : ℝ)`, consumed by the exact ordinary-rank determinant argument. There are no interval variables or subdivisions. Every exported contract additionally passes `#assert_trust kernel`. The independent `Challenge.lean` has 15 deliberate statement placeholders; it is never imported by `Solution.lean`.

## Reproduction

Inside this directory, run:

```sh
lake build Solution
```

The Lean 4.33.1 toolchain and all dependencies are pinned. The recorded macOS development evidence uses direct serial Lean commands; no standalone local Lake build is claimed. GitHub runs the repository's real non-root Linux Comparator. Its exact commit, run IDs and retained artifacts are recorded below.

The [15 statement-first contracts](NUMERICAL_TARGETS.md), [implementation map](IMPLEMENTATION-MAP.json), [metadata](formalization.yaml) and independent review reports retain their precise scopes and source hashes. The pinned Tau Ceti guidance informs AI-agent reviews; no official Tau Ceti service, human peer review or source-author endorsement is claimed.

## Published Linux verification — 19 September 2026 (UTC)

The immutable proof commit is [f488b0cfe2175e5e50d439c5a4115accc4b07b6d](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/f488b0cfe2175e5e50d439c5a4115accc4b07b6d/nonnegative-and-positive-factorizations/NR-04/lean). The [sgstepaniants run 35431159955](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35431159955) and [ajt60gaibb run 35431201248](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35431201248) both passed all 15 exact contracts. Each selected only NR-04 and matched all 165 published project inputs to that revision. The upstream run used GitHub's separately identified synthetic merge commit, with the same proof inputs.

Both runs accepted exported proof bodies using the default Lean kernel and Comparator, permitted only `propext`, `Classical.choice` and `Quot.sound`, and passed the real non-root sandbox and rejection controls. The skipped shared-checker job did not skip these per-proof controls. The [summary](verification/linux-2026-09-19/SUMMARY.json), original GitHub ZIPs, provenance, actual logs and input hashes are retained. The [root audit](verification/linux-2026-09-19/ROOT-AUDIT.json) and [independent evidence review](reviews/runtime-referee-b/REPORT.md) inspect those executions; neither is an additional compiler run.

For the full Linux check, follow the non-root isolation setup in the [repository workflow](../../../.github/workflows/lean-verification.yml), then run the pinned bootstrap and verifier from the repository root:

```sh
tools/lean/bootstrap.sh /tmp/nr04-lean-tools
tools/lean/verify.sh nonnegative-and-positive-factorizations/NR-04/lean /tmp/nr04-lean-tools
```

[Upstream PR #304](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/304) requests inclusion in main. This is one formalized existing resolution; no new mathematical resolution is counted. The copied original audit script records its recovery layout and is not a replacement for the repository verifier.

Archived GitHub API metadata [redacts the contributor’s personal email](verification/PRIVACY-REDACTIONS.json). The redaction manifest preserves hashes of the authenticated original responses and their public derivatives. Proof sources, commit IDs, commands and verification results are unchanged.
