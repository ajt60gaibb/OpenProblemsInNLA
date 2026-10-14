# RA-10 selected projector, idempotence and rank: independent final review

**Source author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE these exact partial spectral gates for aggregate import.

The source-locked `SELECTED_PROJECTOR_PRE_REVIEW.md` is SHA-256 `3e5ebfa4d18de8f47e1ee19e8a29107bf150a0446788f89eea6cd49cc1a3d831` and was independently approved before implementation. Frozen sources are `SelectedProjectionBasic.lean` SHA-256 `cfda9a5c7a4681542e47c967d5a4011e42b28f7cb3891bd3d192a7d336bea22b`, `SelectedProjectionIdempotent.lean` SHA-256 `8ac0fb000300bca16bacdbefe1d0e8c4286418df8bc1c466081e6a1edf966a78`, and `SelectedProjectionRank.lean` SHA-256 `71b13af889493c08dcadb56c749f049cfa34d939e602d8145c3a91de8ac15eb2`.

I checked that `selectedProjection k Q` uses the frozen strict selector `a.val<k` and is exactly `FunctionTruncation k (fun _ => 1) eigenvalues Q` for every eigenvalue vector. Its transpose identity holds without a spectral hypothesis. From every supplied frozen `OrderedPSDSpectralDecomposition`, the idempotence proof uses the actual column orthonormality `QᵀQ=I` and the literal diagonal selector. The rank theorem obtains `rank P=k` for `k≤n` by unit determinant of the square supplied `Q`, invariance of rank under invertible multiplication, and the exact count of selected diagonal ones. These conclusions include `k=0`, `n=0`, ties, and selected zero eigenvalues, without changing the supplied basis.

All three direct pinned Lean 4.33.1 builds passed. My separate imported exact-signature audit `/private/tmp/ra10-selected-projection-independent-audit.lean` is SHA-256 `5e838a88cb26ebca77c5fe19f7fbdfb9bffe7c7028a92ff07574b51c6c456d91`; it checked the public definition and all four theorems with LeanCert `#assert_trust kernel`. The idempotence and rank transitive axiom reports were exactly `[propext, Classical.choice, Quot.sound]`. Source scans found no proof escape. Changed source bytes require a new review.

The supported functional-calculus identity, nuclear pinching contraction, ridge compression, matrix transfer, positive-integral representation, and frozen RA-10 `Target` remain open.
