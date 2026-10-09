# MI-16 Lean statement boundary: independent review

**Verdict: APPROVE.** Reviewer: `/root/inventory_review`, 2026-10-09. This review concerns the exact statement boundary, not a proof of `Target` or the mathematical validity of the supplied resolution.

I compared the canonical problem, the approved pre-implementation specification, and the complete all-spectrum prescription in `solution.tex` with both Lean files. The frozen file differs from the live file only by its freeze comment and namespace. The repository-local import closure consists of `NLA/Statements/Infrastructure.lean`; the remaining direct imports are pinned Mathlib and LeanCert dependencies.

The Lean proposition quantifies over every positive matrix order via `Fin (d + 1)` and every entrywise nonnegative real spectrum. It uses the actual intermediate field `ℚ(λ)` and specializes all critical-locus equations before eliminating. The spectral equation has one factor per distinct eigenvalue. The permanental adjoint deletes row `j` and column `i`; all trace, spectral, commutator, and permanent-value equations are included. `IsCriticalValuePolynomial` characterizes the radical of the univariate elimination ideal through divisibility and positive powers, together with monicity, positive degree, and squarefreeness. Thus its polynomial is the source's monic squarefree critical-value polynomial, not a favorable free choice.

The finite moment expands complete homogeneous polynomials as bounded weak compositions and Schur polynomials by Jacobi–Trudi. Frobenius's coefficient formula gives the ordinary integer character: the exponent is `ν + δ`, the alternant has factors `xᵢ − xⱼ` for `i < j`, and fixed points omitted by Mathlib's `cycleType` are restored as one-cycles. The weight uses `χ(e)/(np)!` and sums `χ(kh)` over every row and column permutation. The moment includes precisely partitions of `np` with at most `n` rows and divides by `sν(1ⁿ)`; the target asserts these denominators are positive at every positive order.

The root list contains all distinct real roots in the closed interval `[0,Lⁿ]`, including potentially infeasible complex-critical values. The multiple-root branch uses the minimum adjacent gap, least qualifying `b`, ceiling `h`, order `p = 2n²bh`, and the source's strict test `T > rⱼ^p`. The zero-spectrum and single-root branches are explicit. The target asserts root/gap/least-integer well-definedness, a unitary attaining the computed answer, and a real upper bound for every unitary orbit permanent. I found no weakening or semantic mismatch in these boundaries.

Pinned local build: `lake build NLA.Statements.MI16 Reviewed.MI16` succeeded with Lean 4.33.1. LeanCert kernel assertions accepted both targets. `#print axioms Target` reported only `propext`, `choice`, and `Quot.sound` in each namespace. This is local typechecking and kernel-boundary verification; it is not the separate Linux Comparator run.

## SHA-256 review inputs

The first nine paths are the exact `tools/lean_statements/check.py` review-input closure. The final solution file was additionally inspected as the mathematical source.

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/MI-16/NUMERICAL_TARGETS.md` | `41fa41fc723c67443cbf64f3b0a4aad6b5090449866d886d0f99234e5668ab01` |
| `docs/lean/statements/MI-16/ORIGINAL.md` | `81cabc2257bb13297711002f19a88ef6b156b28a2fa23140dd5c118deacb10fc` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/MI16.lean` | `59af0d9e2fcaba2b3540cc718804674d76737a2a554ceb307ef39c0038cd891f` |
| `lean-statements/Reviewed/MI16.lean` | `d363fbcd70b0ab340df8944571a9d2b0170bb878dbea11a60d5c3dc1f03cb1e0` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `matrix-inequalities-and-norms/MI-16/README.md` | `81cabc2257bb13297711002f19a88ef6b156b28a2fa23140dd5c118deacb10fc` |
| `matrix-inequalities-and-norms/MI-16/solution.tex` | `57fa815259b0fcfe658e3ed8502d4494cf0c2e8a993c60d647e976468c5232d1` |
