# TR-20 independent pre-implementation specification review

**Verdict: APPROVE.** Reviewer: `/root`, 2026-10-09. I did not author the canonical problem or this specification. This approves the exact proposition design before any TR-20 Lean implementation, not the proof or a future boundary.

I compared every target paragraph with the canonical README. The specification retains the full ordinary-coordinate Segre variety, complex bilinear numerator and denominator with no conjugates, nonisotropic open set, restricted differential and tangent Hessian, existence of a degenerate critical point, and Zariski closure in the full projective space of symmetric matrices. It keeps the reduced hypersurface degree and both exact all-`n≥2` formulas, including `n=2`. It correctly excludes a purely isotropic incidence, an ambient Hessian, finite diagnostics, or a convenient answer-valued degree function. No numerical tolerance or generic restriction on H was inserted.

## SHA-256 inputs

| Path | SHA-256 |
| --- | --- |
| `tensor-computations/TR-20/README.md` | `9e629fcde0eba55790921dd3cee53ea39a895e39ec2aa967f9f184b2aa9e0c4b` |
| `docs/lean/statements/TR-20/ORIGINAL.md` | `9e629fcde0eba55790921dd3cee53ea39a895e39ec2aa967f9f184b2aa9e0c4b` |
| `docs/lean/statements/TR-20/NUMERICAL_TARGETS.md` | `247ce43522ab2e5caec94496fb3ffd6659a84fed4c0b5a064f30b0450c8dd6af` |
