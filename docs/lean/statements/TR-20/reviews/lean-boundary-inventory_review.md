# TR-20 Lean statement boundary: independent review

**Verdict: APPROVE.** Reviewer: `/root/inventory_review`, 2026-10-09. This reviews the exact algebraic and numerical statement boundary, not a proof of the two degree formulas.

I compared the canonical README, approved specification, resolution manuscript, and both Lean files. The frozen file differs only by its freeze comment and namespace; an independent `rfl` check confirmed definitional equality of the two `Target` propositions. The repository-local import closure is the shared statement infrastructure.

The parameter type has one complex coordinate per unordered pair of Segre entries, exactly the full symmetric `mn×mn` matrix space. The rank-one state is the actual `a⊗b` entry vector, with no binomial weighting, and every pairing is complex bilinear without conjugation. On the nonisotropic locus, `aᵀa` and `bᵀb` are nonzero. The constraints `aᵀu=0`, `bᵀv=0` therefore give a full complement to the two radial directions and model the entire projective Segre tangent space. `Critical` tests every such tangent direction. `HessianNumerator` includes both first-variation terms and the mixed second variation from the Segre embedding; at a critical point its value is a nonzero scalar multiple of the restricted quotient Hessian. `Degenerate` requires a nonzero tangent vector in the radical against every tangent vector. These conditions are invariant under changing nonzero projective representatives.

The critical-degenerate incidence excludes the isotropic denominator and the zero symmetric matrix. `VanishesOnIncidence` uses every polynomial vanishing on that image, so `InDiscriminantClosure` is its genuine affine-cone Zariski closure in the symmetric parameter coordinates. `HasReducedHypersurfaceDegree` requires a nonzero, nonunit homogeneous polynomial generating the **entire** vanishing ideal, with exact total degree. Since that ideal is radical, this records the reduced hypersurface degree rather than a repeated eliminant. `Target` asserts both hypersurface degree formulas for every `n≥2`, including `n=2`, with exact natural binomial coefficients and no generic-metric qualification. I found no lost boundary condition or numerical weakening.

Pinned local `lake build NLA.Statements.TR20 Reviewed.TR20` succeeded with Lean 4.33.1. LeanCert kernel assertions accepted both targets. `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. This is local boundary verification, not the separate Linux Comparator run.

## SHA-256 review inputs

The first nine paths are precisely the `tools/lean_statements/check.py` `lean-boundary` closure. The manuscript TeX was additionally inspected.

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/TR-20/NUMERICAL_TARGETS.md` | `247ce43522ab2e5caec94496fb3ffd6659a84fed4c0b5a064f30b0450c8dd6af` |
| `docs/lean/statements/TR-20/ORIGINAL.md` | `9e629fcde0eba55790921dd3cee53ea39a895e39ec2aa967f9f184b2aa9e0c4b` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/TR20.lean` | `4d6373292218fe0cce2be3a01ce9fe30a0675d6f6aaf091f86d098065dbef39b` |
| `lean-statements/Reviewed/TR20.lean` | `8c9a4e8b8dff89747488bace4b8393665828cda9fc34f3b986210bf783b3ce47` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `tensor-computations/TR-20/README.md` | `9e629fcde0eba55790921dd3cee53ea39a895e39ec2aa967f9f184b2aa9e0c4b` |
| `references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-20.tex` | `8a9b6ca32e30c17491742444fba96f72941a01a555b33032ef0277e419aa0a38` |
