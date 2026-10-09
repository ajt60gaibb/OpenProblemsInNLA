# TR-20 pre-implementation specification: independent review

**Verdict: APPROVE.** Reviewer: `/root/inventory_review`, 2026-10-09. This approval concerns fidelity of the mathematical and numerical statement, not a Lean implementation or new proof of the cited resolution.

I compared the complete canonical README, its byte-identical `ORIGINAL.md`, the proposed specification, and the resolution manuscript's Theorem 1 and parameter-space discussion. The specification fixes the true Segre projective rank-one locus in ordinary complex entry coordinates, and keeps the *full projective symmetric-matrix* parameter space rather than silently replacing it by the space of `(2,2)` sections. It uses `ψᵀHψ / ψᵀψ` with complex-bilinear transpose, not conjugation. It excludes the exact isotropic boundary `ψᵀψ=0` from the critical-degenerate incidence, takes the Hessian on the full Segre tangent space at a critical point, and then takes the Zariski closure of those parameters.

It asks that both `m=2` and `m=3` loci be hypersurfaces and that their **reduced** projective degrees equal `24·binomial(n+1,3)` and `24·n²·binomial(n,2)` respectively for every integer `n≥2`. This matches the original conjecture and the manuscript's requested formulas, including the distinction between a reduced image degree and a ramification-scheme count. The specification correctly notes that passing to all `(2,2)` sections requires the source's surjective, degree-preserving pullback argument. I found no altered incidence, omitted boundary convention, or weakened numerical range.

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-20/README.md` | `9e629fcde0eba55790921dd3cee53ea39a895e39ec2aa967f9f184b2aa9e0c4b` |
| `docs/lean/statements/TR-20/ORIGINAL.md` | `9e629fcde0eba55790921dd3cee53ea39a895e39ec2aa967f9f184b2aa9e0c4b` |
| `docs/lean/statements/TR-20/NUMERICAL_TARGETS.md` | `247ce43522ab2e5caec94496fb3ffd6659a84fed4c0b5a064f30b0450c8dd6af` |
| `references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-20.tex` | `8a9b6ca32e30c17491742444fba96f72941a01a555b33032ef0277e419aa0a38` |
