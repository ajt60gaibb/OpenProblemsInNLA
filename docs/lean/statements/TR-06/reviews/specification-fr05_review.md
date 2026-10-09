# TR-06 independent specification review

**Verdict: APPROVE.** Reviewer: `/root/fr05_review`, 2026-10-09. I did not author the canonical source, `ORIGINAL.md`, `NUMERICAL_TARGETS.md`, or Lean implementation. This review was conducted after the Lean files were drafted, as an additional independent check of the pre-implementation specification; the infrastructure and inventory reviewers recorded their specification approvals before implementation. This approves the mathematical statement specification, not a Lean implementation or a proof of integrability.

`ORIGINAL.md` is byte-identical to the permanent README. The specification keeps every tensor order `d≥3`, every factor dimension `n_j≥2`, and every `r≥3` subject to *generic complex* identifiability. It retains the real smooth identifiable rank-`r` locus, its induced Euclidean volume, and the actual volume-Gaussian normalizer. The condition number uses the derivative of the local inverse after *individual* Frobenius normalization of each nonzero summand. The strict conclusion is finite expectation for each format, with no claimed uniform constant. This matches the canonical problem and the source manuscript's theorem and regular-locus/full-measure discussion in §§1 and 3–4.

The specification explicitly permits changing values or extending integrands on a `μ`-null exceptional set. Any later Lean implementation that uses a regular addition-map branch as `M_r` still needs mathematical justification that omitted identifiable smooth points have lower dimension and zero induced volume. The manuscript §3 supplies that justification; it is not a license to replace the volume measure by an arbitrary parameter law.

## SHA-256 review inputs

| Path | SHA-256 |
| --- | --- |
| `tensor-computations/TR-06/README.md` | `f364f4b2ad51065c17d7dd08ea32e729a5d53a8333f0785a11a368165942de6b` |
| `docs/lean/statements/TR-06/ORIGINAL.md` | `f364f4b2ad51065c17d7dd08ea32e729a5d53a8333f0785a11a368165942de6b` |
| `docs/lean/statements/TR-06/NUMERICAL_TARGETS.md` | `ccc0528ad0404fcd6b5e7d3fcb31e68a65904fd631e052417fcd281480d60a16` |
| `references/colbrook-unclaimed-2026-09-11/manuscripts/TR-06.md` | `65f9b731628a7a9ab0580d8522cead94bf7e4599ee3c4285e485287d35d451b2` |
