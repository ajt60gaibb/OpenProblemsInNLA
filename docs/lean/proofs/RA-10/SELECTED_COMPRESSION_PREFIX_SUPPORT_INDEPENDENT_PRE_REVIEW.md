# RA-10 support of the positive compression prefix: independent pre-review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE exact supplied-basis reconstruction and positive-prefix support for staged Lean implementation.

I checked `SELECTED_COMPRESSION_PREFIX_SUPPORT_PRE_REVIEW.md` at SHA-256 `75a8af4c0786b94bb219845c70a0d222f9dd3964ac3fed562eebab50f1ec2e02` against the unchanged RA-10 source, frozen ordered PSD predicate, audited positive-eigenvector helper, Parseval gate, and nonzero-intersection theorem. All source hashes match. A supplied square orthonormal real Q has both `QᵀQ=I` and `QQᵀ=I`, so the proposed coordinate expansion reconstructs every vector exactly in the same Q, including tied or zero eigenspaces and empty dimension.

If `eigenvaluesC a>0`, antitonicity makes every C eigenvalue at `b≤a` positive. The audited helper fixes each corresponding supplied `QC` column under the actual selected `P=selectedProjection k QAhat`. A vector whose strict QC suffix coordinates vanish is their linear combination by exact reconstruction, hence `P*ᵥx=x`. The theorem retains `hAhat` and an ordered decomposition of the **actual** `C=PAP`; it does not assume support of x or change the basis. The k=0 positive-eigenvalue premise is impossible for the zero compression, and no special gap or normalization is needed.

Approval covers the two exact proposed signatures, with reconstruction allowed as a separately frozen stage. Each implementation requires pinned LeanCert kernel checking and independent imported exact-signature/source/axiom audit before aggregate import. Equality of C/A quadratic forms on this range, cancellation, compression min-max, nuclear inequalities, and full RA-10 Target remain open.
