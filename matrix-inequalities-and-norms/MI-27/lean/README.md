# MI-27: coefficient one in the logarithmic commutator inequality

Formalization by **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology**, with substantial Codex assistance. The analytic resolution remains credited to **Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation**.

`NLA.MI27.logarithmic_commutator_bound` proves the unchanged original inequality for every positive dimension and every complex positive definite pair with trace sum one. It uses the actual spectral natural logarithm and Gram-square-root trace norm. Neither the relative-entropy identity nor its derivative is assumed in the final theorem. The source manuscript's separate order-two optimality result is not included in the advertised formalization.

## Verification status

All twenty frozen contracts pass actual local serial Lean in recovery-118. The [recursive local audit](verification/local-2026-09-19/LOCAL-REPLAY-AUDIT.json) binds 52 proof modules, actual commands, source/output hashes and successful source-matched dependency reuse. The coordinator allows only one compiler, one thread and 4096 MiB. The [transitive axiom reports](verification/local-2026-09-19/actual-axioms.json) contain only standard Lean axioms. An [isolated local diagnostic](verification/type-preflight-118/AUDIT.json) found all twenty elaborated types and universe lists byteidentical to the frozen Challenge.

Two wholly nonauthor final source reviews passed: [referee B](reviews/final-referee-b/REPORT.md) and [newmath referee](reviews/final-newmath/REVIEW.md). Each independently authenticated the actual saved local evidence without rerunning the compiler. Real GitHub Linux Comparator verification remains pending. Local type diagnostics are not Comparator. This phase does not change the canonical mathematical status or completed verification count. [STATE.md](STATE.md) records the immutable review snapshot and supersedes earlier draft source comments; [STATE.json](STATE.json) records the current publication phase.

## Proof structure and computation

The proof derives a dimension-independent positive-commutator bound, an endpoint-optimizer bound along actual unitary flow, and one cutoff valid for all unitary conjugates. It proves the ordinary noncommuting relative-entropy identity internally using negative spectral counts, congruence invariance, scalar pencil integration and Fubini with prior integrability. Mixture terms are truncated before substitution. Finite kernel integrals then bound entropy change; the actual noncommuting trace derivative and a spectral-sign witness give coefficient exactly one. Repeated eigenvalues, zero commutators and the degenerate finite interval remain included.

Kernel-mode LeanCert proves only the fixed exact inequality `0 < 1/2`, consumed in the positive-commutator argument. There are no interval variables, subdivisions or numerical quadratures. Every exported theorem also passes `#assert_trust kernel`. The twenty deliberate reference placeholders in `Challenge.lean` are never imported by the proof environment. Seven retained MI24 modules support the proof and do not count as an additional formalized problem.

The [numerical plan](NUMERICAL_TARGETS.md), [implementation map](IMPLEMENTATION-MAP.json), [metadata](formalization.yaml), frozen contracts and source context document the full scope. The proof's C10 cutoff is R=1+M/epsilon with M=norm(rho)+norm(sigma)+1; this sound construction proves the unchanged existential contract and supersedes the plan's simpler suggested cutoff.

## Reproduction

Inside this directory, with the pinned Lean 4.33.1 toolchain:

```sh
lake build Solution
```

This is the usual standalone build command; the recorded macOS development runs instead use the retained direct serial Lean commands with one thread and 4096 MiB. All dependencies are pinned. For final Comparator, follow the non-root Linux isolation setup in [the workflow](../../../.github/workflows/lean-verification.yml), then from the repository root run:

```sh
tools/lean/bootstrap.sh /tmp/mi27-lean-tools
tools/lean/verify.sh matrix-inequalities-and-norms/MI-27/lean /tmp/mi27-lean-tools
```

The pinned Tau Ceti rubrics inform AI-agent review; no official Tau Ceti execution, human peer review or source-author endorsement is claimed. Schiffer and Forsythe supplied inspected statement/workflow patterns, not imported mathematical results. Real Linux run IDs and exact published commits will be added only after successful executions.
