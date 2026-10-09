# TR-17 independent Lean-boundary review

**Verdict: APPROVE.** Reviewer: `/root`, 2026-10-09. I did not author the live or frozen Lean boundary. This reviews the statement meaning, not a proof of the ED-degree inequality.

I compared the canonical README, the approved numerical target, and the concrete shared geometry imported by both Lean boundaries. `Coord` indexes the coefficient coordinates of each symmetric factor, `monomial` gives the scalar Segre–Veronese parameterization, and its kernel gives the full affine complex cone ideal. The quantified formats have `k≥1`, `n_j≥2`, `d_j≥1`, and total order at least three. `Form` and `PositiveDefinite` quantify every real symmetric positive definite matrix in these coordinates. The `objective` uses the complex-bilinear extension of that form and independent generic datum coordinates over their fraction field, with no complex conjugation.

`weight` counts ordered entries represented by each symmetric coordinate, so diagonal `Frobenius` is the restriction of the entrywise tensor inner product, including repeated-entry weights. The cone codimension is the ambient coordinate count minus `1+∑(n_j−1)`. `criticalIdeal` includes the cone ideal and all maximal minors of the matrix formed by the objective gradient and gradients of arbitrary cone-ideal elements. On the smooth nonzero cone, this is precisely the criticality rank condition. Saturation by the origin ideal removes the excluded vertex. `CriticalScheme` is the resulting quotient over the generic-data field; its vector-space dimension counts finite algebraic solutions with scheme multiplicity. `GenericFinite` explicitly requires finite generic fibers for both metrics, rather than letting an infinite quotient silently become a numerical degree.

`Claim` compares the Frobenius scheme length to the scheme length for every admissible positive definite metric; it does not impose a generic metric, reduced fiber, or real critical-point restriction. I independently ran the pinned live/frozen Lake build and a separate `Target = Reviewed.Target := by rfl` check. Both passed; LeanCert kernel trust reported only `propext`, `Classical.choice`, and `Quot.sound`. The equivalence of this Jacobian-minor quotient length to the manuscript's generic ED critical-point multiplicity is a mathematical review judgment at the specification boundary, not a Lean proof.

## SHA-256 review inputs

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/TR-17/NUMERICAL_TARGETS.md` | `08d4027ca2d185945da636498173fb90fcec4d5d565a22a839090ea6c94eb120` |
| `docs/lean/statements/TR-17/ORIGINAL.md` | `d5fd05e1116e654027debc79f16c432f3b02a3034d52a7b54247ea788f63c3ca` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/Shared/TR17Geometry.lean` | `1ece781afa1117b05bbe672d6e3c3c434ef1550bae859513825c63e43c61ea94` |
| `lean-statements/NLA/Statements/TR17.lean` | `b4142004f20a6935125b1a42aaaf8131376c4813a651f7d578cde59deb82ba0b` |
| `lean-statements/Reviewed/TR17.lean` | `a0075329a851c7966849eb0acd767d61df0141bb8c174ee74786013d1d278e3e` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `tensor-computations/TR-17/README.md` | `d5fd05e1116e654027debc79f16c432f3b02a3034d52a7b54247ea788f63c3ca` |
