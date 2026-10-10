# RA-10 actual selected compression PSD: independent pre-review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact quadratic and frozen PSD propositions for Lean implementation.

I reviewed `SELECTED_COMPRESSION_PSD_PRE_REVIEW.md` at SHA-256 `f1fa522eb88da80d67174ef6f468169dffd6bf5d221950139ecaca8df4f60816` against the frozen RA-10 statement, source `C=PAP`, audited spectral PSD theorem, and actual supplied selected projection. The first proposed identity expands `xᵀ(PAP)x` exactly as `(Px)ᵀA(Px)` because the selected `P` is symmetric; the `Matrix.mulVec` orientation is `y_i=Σ_j P_ij x_j`. With the supplied decomposition of `A`, this yields the frozen quadratic nonnegativity of the **actual** `C`, and `Pᵀ=P`, `Aᵀ=A` give the frozen symmetry conjunct. No entrywise positivity or operator-norm shortcut is used. The identities include `n=0`, `k=0`, `k≥n`, tied and zero eigenvalues, and do not require `QA=QAhat`.

Approval covers the two displayed exact Lean declarations only. It does not produce an ordered spectral decomposition of `C` or establish the nuclear inequality, compression eigenvalue bounds, Lemma 2, integral transfer, or full Target. Freeze the implementation for separate imported exact-signature and LeanCert kernel/axiom audit.
