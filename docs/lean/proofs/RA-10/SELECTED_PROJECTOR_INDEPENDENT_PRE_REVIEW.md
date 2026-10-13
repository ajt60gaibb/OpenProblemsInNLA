# RA-10 selected spectral projector: independent pre-implementation review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact selected-projector gate for Lean implementation.

I reviewed `SELECTED_PROJECTOR_PRE_REVIEW.md` at SHA-256 `3e5ebfa4d18de8f47e1ee19e8a29107bf150a0446788f89eea6cd49cc1a3d831` against the locked frozen RA-10 definitions and solution. The literal strict zero-based selector is `a.val<k`; `selectedProjection k Q` is exactly `FunctionTruncation k (fun _ => 1) eigenvalues Q` for every eigenvalue vector. The frozen decomposition supplies `QᵀQ=I` through its stated column sums; since `Q` is square, it is invertible with inverse `Qᵀ`, so `QQᵀ=I`. Writing `P=QDQᵀ` with `Dₐₐ=1` exactly on `a.val<k` gives `Pᵀ=P`, `P²=P`, and rank `min(k,n)`. With `k≤n`, the proposed rank theorem is exactly `k`; this includes `k=0` and `n=0`.

The supported functional-calculus identity `P·FunctionMatrix f eigenvalues Q·P=FunctionTruncation k f eigenvalues Q` holds for every real function `f`, including `f(0)>0`, because multiplication by `P` removes the complementary spectral components. It preserves the chosen supplied `Q` through ties and zero selected eigenvalues. The final target's `k<n` entails the local rank premise. No gap, PSD strengthening, favorable basis, or new final-target hypothesis is introduced.

Approval covers these exact matrix equalities and rank claim. The frozen nuclear-norm contraction, ridge compression, integral representation, and `TransferBound 11` remain open. Freeze each implemented module for an independent imported exact-signature and LeanCert kernel audit before aggregate import.
