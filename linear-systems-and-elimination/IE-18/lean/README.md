# IE-18 Lean formalization

This project proves a negative answer to the [original IE-18 identity](../README.md). For `M=diag(1/10,1/2,3/5)` and `v=(1,1,1)`, two executions of the actual Anderson residual map have squared norm ratio `1920682/21289638243 > 1/14641`. The true eigenvalue-pair maximum is `1/121`, so the actual **unsquared** ratio exceeds the proposed factor. Both `M` and `I−M` are proved positive definite.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. Original mathematical counterexample and informal proof: **Matthew J. Colbrook**. [formalization.yaml](formalization.yaml) records the sources, roles and automation.

The complete proof builds under pinned Lean 4.33.1. Two independent final proof referees re-elaborated the source successfully. All eight audited internal results and exports pass `#assert_trust kernel` and report exactly `propext`, `Classical.choice`, and `Quot.sound`. [Authoritative Linux Comparator passed on 12 September 2026](verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) at immutable revision `7b8512e21c50adc8597dcdbed32f2aec13c3b43e`. The catalog entry now records `Lean verified` for the complete original negative target.

## Reviewed statements and proof

[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md), [Definitions.lean](NLA/IE18/Definitions.lean) and [Challenge.lean](Challenge.lean) were written, typechecked and approved by two independent statement referees before implementation. [Proof.lean](NLA/IE18/Proof.lean) derives both residuals and their nonzero denominators, proves admissibility, and evaluates the maximum over the actual Mathlib Hermitian eigenvalues.

[Solution.lean](Solution.lean) exports:

- `NLA.IE18.residual_certificate`: the actual two map evaluations, denominators, coefficients and squared norm ratio.
- `NLA.IE18.counterexample`: all admissibility facts, the actual spectral maximum and a strict violation of the claimed greatest amplification.
- `NLA.IE18.not_fourStepConjecture`: negation of the complete original universal identity.

The maximum proof uses spectral membership and attainment with actual indices; it does not compute a chosen eigenbasis. Exact rational algebra and nine scalar pair cases reduce LeanCert to one rational comparison in explicit kernel mode. A proved nonnegative-square bridge recovers the unsquared norm inequality without approximating square roots or subdividing intervals. The source's stronger parameter family and separate asymptotic convergence question are outside this formalization's scope.

## Reproduction and evidence

From this directory, the development build is:

```bash
lake exe cache get
lake build Solution
```

All dependency revisions are fixed in `lake-manifest.json`. The three deliberate Challenge placeholders belong to a separate target environment and are never imported by Solution. Frozen statement and referee records are in [reviews/](reviews/); the build, axiom and independent re-elaboration logs are in [verification/](verification/).

From the repository root on the supported non-root Linux host, use the [shared harness prerequisites](../../../tools/lean/HARNESS.md) and:

```bash
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py linear-systems-and-elimination/IE-18/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh linear-systems-and-elimination/IE-18/lean /absolute/path/to/nla-lean-tools
```

The project must be committed and unchanged. The harness checks fresh inputs in the real Linux sandbox, runs positive and negative controls, and applies [Comparator](comparator.json). Formal identity and kernel acceptance supplement independent English-to-Lean fidelity review. The [retained Linux result and raw logs](verification/linux-2026-09-12/) bind the successful run to the immutable proof revision. The remote Ubuntu run used fresh project inputs and the matching official Mathlib dependency cache; the Mac-based referee checks are recorded separately.
