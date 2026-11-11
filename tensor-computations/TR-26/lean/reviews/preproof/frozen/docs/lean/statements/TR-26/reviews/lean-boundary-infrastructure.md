# TR-26 independent Lean boundary review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the TR-26 specification, live Lean source, or frozen source. Phase: `lean-boundary`. Verdict: **APPROVE** for the exact statement boundary. This reviews the statement, not a proof of either degree formula or external human peer review.

## Exact `check.py` review inputs

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-26/README.md` | `56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659` |
| `docs/lean/statements/TR-26/ORIGINAL.md` | `56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659` |
| `docs/lean/statements/TR-26/NUMERICAL_TARGETS.md` | `630e5dfb41a844e1105fc9af698520458449e1b58336b23d182e16d292114624` |
| `lean-statements/NLA/Statements/TR26.lean` | `e0b38f44232ea35418e8afb9bcd0c1df0e2dd51642cda71e8bf62564a130095f` |
| `lean-statements/Reviewed/TR26.lean` | `e1700dde28c3679f126eaae1ea7cb16e979a18e94f1e77d198996f0f6ede6820` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

These are all paths returned by `tools/lean_statements/check.py` `review_inputs` for TR-26's `lean-boundary` phase. The canonical README and `ORIGINAL.md` are byte identical; `Infrastructure.lean` is the only repository-local import. The frozen source is exactly the live source under the permanent-ID namespace substitution plus the standard frozen header.

## Exact scheme, geometry, and degree comparison

`veronese` uses the source's unweighted `[a^d:a^(d−1)b:…:b^d]` coordinates. The scalar `c` in `OnCurve` makes every nonzero affine representative available and includes the point at infinity. The symmetric matrix parameter type stores exactly its independent upper-triangle complex entries; `symmetricEntry` reconstructs the full symmetric matrix. `numerator` and `denominator` use ordinary complex-bilinear transposes, never conjugation. `OpenCritical` requires nonzero `H`, a nonisotropic curve point, and vanishing of the quotient derivative in both homogeneous parameter directions. Their span contains the curve tangent and radial direction at every point, including infinity, so this is exactly criticality along the projective curve.

`VanishesOnOpen` is the entire polynomial vanishing ideal of the open critical correspondence in the affine cone, with independent scaling of curve and matrix representatives. `Incidence` takes its common zeros at nonzero projective representatives, which is the source's Zariski closure, while retaining the exact curve. `JacobianSpace` spans the `z` partial derivatives of **every** polynomial in that full ideal. At an incidence point this is the same conormal span as any homogeneous ideal-generating family, so `Module.finrank ≤ d−1` preserves the source's Jacobian-rank threshold and scheme structure. It is not the Jacobian of a chosen shortcut critical equation.

`IsotropicImage` projects `Ramification ∩ {zᵀz=0}` exactly, with no additional closure. `NonisotropicImage` projects the complementary ramification points, and `NonisotropicClosure` takes its separate projective Zariski closure in the full symmetric-matrix coordinates. `HasReducedDegree` requires a nonzero **squarefree homogeneous** polynomial cutting out each entire projective set; its homogeneous degree is exactly the reduced hypersurface degree, including all components and excluding eliminant multiplicity. `Target` asserts both `6(d−1)` and `2d` for **every** `d≥2`, including the `d=2` endpoint. I found no swapped component, lost closure, weakened degree, or changed geometry.

## Kernel and frozen identity checks

With pinned Lean 4.33.1, `lake build NLA.Statements.TR26 Reviewed.TR26` passed (8710 jobs). Both `#assert_statement` and `#assert_trust kernel` passed; printed axiom closure is `propext`, `choice`, `Quot.sound`. A fresh file importing both modules proved

```lean
example : NLA.Statements.TR26.Target = NLA.ReviewedStatements.TR26.Target := by rfl
```

No TR-26 Lean source was edited in this review.
