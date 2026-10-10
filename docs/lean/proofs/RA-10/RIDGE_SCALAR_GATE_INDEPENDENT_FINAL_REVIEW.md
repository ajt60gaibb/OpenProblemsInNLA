# RA-10 ridge scalar identities and finite tail: independent final review

**Source author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE these exact scalar partial gates for aggregate import.

The independently approved mathematical/numerical precontract is `RIDGE_SCALAR_GATE_INDEPENDENT_PRE_REVIEW.md` against the author contract SHA-256 `325fc8c9a9e32c35aec0e29d04b770891094bb9477e868697833e337dbc122e7`. The frozen Lean source `lean-statements/NLA/Proofs/RA10/RidgeScalar.lean` is SHA-256 `5eab9a208a8fa9cb3f7c5cfa7ad0888ff3a0ac4c23f1236ee6166f6f1eaf792f`.

I checked the public definition `ridgeAtom s x = x/(s+x)` and the exact source Equation (12), with coefficient `s/((s+a)(s+b))` and the sharp upper coefficient `1/(s+c)` under `s,c>0`, `a≥c`, `b≥0`. The pointwise Equation (20) uses `0≤x≤c`. The finite version sums precisely over `{i : Fin n | k≤i.val}`, the zero-based form of source `i>k`; it allows `n=0` and an empty tail. No gap, numerical approximation, or new final-target premise is introduced.

The direct pinned Lean 4.33.1 build passed. My separate imported exact-signature audit `/private/tmp/ra10-ridge-scalar-independent-audit.lean` is SHA-256 `a4f72ab5fbdec14ce6163510fb799c00f8c1b9584a4394c22af1ca4053562ccf`; it checked the public definition and all four theorems and ran LeanCert `#assert_trust kernel`. Both printed axiom reports were exactly `[propext, Classical.choice, Quot.sound]`. The source has no proof escape. Changed source bytes require a new review.

This gate does not prove the matrix compression estimate, nuclear-norm transfer, positive-integral representation, `TransferBound 11`, or frozen RA-10 `Target`.
