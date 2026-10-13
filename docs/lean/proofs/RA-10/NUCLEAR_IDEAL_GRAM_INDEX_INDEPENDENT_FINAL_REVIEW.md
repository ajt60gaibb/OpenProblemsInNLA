# RA-10 ordered Gram eigenvalue to singular value: independent final review

**Disposition:** approved for aggregate import as the exact same-index Gram bridge. The pointwise singular-value ideal inequality, its nuclear-norm sum, Eq. (14), and full RA-10 Target remain open.

I independently inspected `NuclearIdealGramIndex.lean` at SHA-256 `0dad977bffe7fedb6f5eb9483613a7aebe17c8da19ab82b31ecf4cf0a9cca0f8` against the approved exact precontract and frozen `Statements/RA10.lean`. The public theorem accepts **any** frozen ordered PSD decomposition of `YᵀY` and returns `g i = singularValues(toEuclideanLin Y, i.val)^2` for each zero-based `i:Fin n`, including tied/zero values and `Fin 0`.

The source identifies the actual Gram matrix with `Y.adjoint ∘ Y` under the Euclidean linear-map equivalence. It constructs a canonical sorted Mathlib Gram witness using the explicit `sortedHermitianIndex`. The canonical matrix eigenvalue matches the linear-map eigenvalue at the same `Fin (card (Fin n))` index through equality of operator characteristic polynomials, then uses pinned `sq_singularValues_fin`. Two applications of the audited same-index Loewner theorem to the zero matrix difference identify an arbitrary supplied `g` with this canonical list. No spectrum permutation, rank assumption, nonzero-dimension assumption, or numerical factor is introduced.

Separate imported audit `/private/tmp/ra10-gram-index-independent-audit.lean` at SHA-256 `7081283287890dee46fb6934cc1c70fa2f22cad9aae3dd6a6f67253af3790259` restated the exact public signature and passed pinned Lean 4.33.1 with LeanCert `kernel`. `#assert_trust` passed and `#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`. Source scan found no `sorry`, `admit`, `native_decide`, `unsafe`, or custom axiom.
