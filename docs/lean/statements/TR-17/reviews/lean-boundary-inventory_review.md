# TR-17 Lean statement boundary: independent review

**Verdict: APPROVE.** Reviewer: `/root/inventory_review`, 2026-10-09. This checks the exact statement boundary, not a proof of Frobenius minimality.

I compared the canonical README, approved specification, resolution manuscript, live Lean target, frozen target, and complete repository-local import closure. The coordinate type uses one symmetric-power monomial index in each factor. `monomial` maps it to a scalar multiple of the product of factor monomials, so `coneIdeal` is the actual Segre–Veronese cone ideal, including zero. The independent generic datum is represented by the fraction field of complex polynomial coordinates. The objective uses a complex-bilinear extension of every real metric coefficient, with no conjugation.

`criticalIdeal` adds all maximal minors of the objective gradient and gradients of arbitrary cone-ideal equations. At the smooth nonzero locus the cone Jacobian has the declared codimension, so these minors impose the complete tangent criticality condition. Saturation by powers of the origin ideal removes components supported at the singular origin; it does not discard nonzero isotropic or complex critical points. `CriticalScheme` is the resulting generic coordinate-ring quotient. `GenericFinite` requires a finite generic fiber, and its vector-space dimension records scheme length, including algebraic multiplicities rather than only distinct or real solutions.

The Frobenius diagonal weight counts every ordered tuple realizing a symmetric multiset, multiplied across factors; this is exactly the repeated-entry weight from the full unsymmetrized tensor. `PositiveDefinite` quantifies over all nonzero real coordinate vectors and requires symmetry. The claim covers every `k≥1`, all `n_j≥2`, `d_j≥1` with total order at least three, and every positive definite metric. It asserts both relevant generic degrees are finite and the exact natural-number inequality, without imposing a generic metric or reducing to a local comparison. I found no numerical or semantic weakening.

Pinned `lake build NLA.Statements.TR17 Reviewed.TR17` passed. An independent `rfl` example established equality of the live and frozen `Target` propositions. LeanCert kernel assertions passed; `#print axioms` listed only `propext`, `Classical.choice`, and `Quot.sound`. This verifies the local statement boundary, not the separate Comparator environment.

## SHA-256 review inputs

The first ten paths are the `tools/lean_statements/check.py` `lean-boundary` closure. The resolution manuscript was additionally inspected.

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/TR-17/NUMERICAL_TARGETS.md` | `08d4027ca2d185945da636498173fb90fcec4d5d565a22a839090ea6c94eb120` |
| `docs/lean/statements/TR-17/ORIGINAL.md` | `d5fd05e1116e654027debc79f16c432f3b02a3034d52a7b54247ea788f63c3ca` |
| `lean-statements/NLA/Statements/Shared/TR17Geometry.lean` | `1ece781afa1117b05bbe672d6e3c3c434ef1550bae859513825c63e43c61ea94` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/TR17.lean` | `b4142004f20a6935125b1a42aaaf8131376c4813a651f7d578cde59deb82ba0b` |
| `lean-statements/Reviewed/TR17.lean` | `a0075329a851c7966849eb0acd767d61df0141bb8c174ee74786013d1d278e3e` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `tensor-computations/TR-17/README.md` | `d5fd05e1116e654027debc79f16c432f3b02a3034d52a7b54247ea788f63c3ca` |
| `references/colbrook-tensor-metrics-rank-2026-09-11/manuscripts/tr17_solution.tex` | `abbaff0249f941e745810173e425b6ce424a0915066088ebdba8f6fc5e9548cb` |
