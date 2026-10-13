# RA-10 spectral quadratic form: independent final review

**Source author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this exact partial gate for aggregate import. Constant-eleven transfer and the frozen RA-10 Target remain open.

The exact mathematical statement was independently approved before implementation in `SPECTRAL_QUADRATIC_GATE_INDEPENDENT_PRE_REVIEW.md`, against the author contract SHA-256 `5697cd4d02a0c3fa37202fa7e9c31173e8f23f33046bc0bce1427f0b67d198fc`. The frozen source `lean-statements/NLA/Proofs/RA10/SpectralQuadratic.lean` is SHA-256 `23e82984e32c8724fda21446037db91ca0180f52d41602dde086d16a1f954eae`.

I read the full source. The first theorem expands the literal frozen `SpectralMatrix` entry and rearranges only finite sums to obtain the exact square formula for every `n`, including zero. The second uses the supplied frozen eigendecomposition's original `A`, eigenvalues and `Q`; it proves symmetry and the literal frozen nonnegative quadratic form using nonnegative eigenvalues, without selecting a new basis or assuming gaps or invertibility. The source has no proof escapes or custom axioms.

The pinned Lean 4.33.1 direct module build passed 2,725 jobs. A separate imported exact-signature audit `/private/tmp/ra10-spectral-quadratic-independent-audit.lean` (SHA-256 `1941bec5e283bdbaca50a9179c9c38fecf5231e6ee19b2d76189d6c604ea14c9`) checked both public theorems and two `#assert_trust kernel` directives. `#print axioms` returned only `[propext, Classical.choice, Quot.sound]`. Aggregate build is recorded in PR verification after import.

This gate does not prove nuclear-norm or functional-calculus equivalence, ridge compression, the general operator-monotone integral representation, `TransferBound 11`, or `Target`.
