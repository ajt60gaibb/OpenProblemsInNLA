# TR-26 independent Lean-boundary review

**Verdict: APPROVE.** Reviewer: `/root`, 2026-10-09. I did not author the TR-26 specification, live Lean module, or frozen module. This verifies exact statement meaning, not the two degree theorems.

I compared the complete canonical problem with the pre-implementation specification and both Lean files. `veronese` uses exactly `[a^d:a^(d−1)b:…:b^d]` with no binomial weights and includes the point at infinity. `SymIndex` gives precisely the independent upper-triangle entries of every complex symmetric matrix. Numerator and denominator use ordinary complex bilinear transpose; no conjugate operation appears. `OpenCritical` requires nonzero matrix, a nonzero curve point, a nonzero denominator, and vanishing of the quotient differential in both parameter directions, which spans the curve tangent including at infinity.

The open incidence is separately scaling invariant in `z` and `H`. `VanishesOnOpen` is its full polynomial vanishing ideal and `Incidence` is the common-zero closure intersected with the exact curve and nonzero projective representatives. `JacobianSpace` spans all `z`-partial derivatives of the full ideal; at a common zero this agrees with the span of derivatives of any generating set. `Ramification` imposes exactly rank at most `d−1`. The isotropic image is the raw projection of `B∩Q`; the nonisotropic image is projected after excluding `Q` and then Zariski closed. These are distinct constructions as in the source.

`HasReducedDegree` requires a squarefree homogeneous polynomial in the actual symmetric-parameter ring whose zero set is exactly the nonzero projective set, so its total degree is the reduced hypersurface degree. `Target` includes both all-`d≥2` formulas `6(d−1)` and `2d`, including `d=2`, with no finite diagnostic or total-degree substitution.

I independently reran the pinned live/frozen Lake build and a separate `Target = Reviewed.Target := by rfl` check; both passed. LeanCert kernel trust found only the three standard axioms. This is a statement-boundary check, not a proof or a Linux Comparator run.

## SHA-256 review inputs

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/TR-26/NUMERICAL_TARGETS.md` | `630e5dfb41a844e1105fc9af698520458449e1b58336b23d182e16d292114624` |
| `docs/lean/statements/TR-26/ORIGINAL.md` | `56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/TR26.lean` | `e0b38f44232ea35418e8afb9bcd0c1df0e2dd51642cda71e8bf62564a130095f` |
| `lean-statements/Reviewed/TR26.lean` | `e1700dde28c3679f126eaae1ea7cb16e979a18e94f1e77d198996f0f6ede6820` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `tensor-computations/TR-26/README.md` | `56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659` |
