# RA-10 exact ordered spectral Rayleigh bounds: independent pre-review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact Parseval and coefficient-one prefix/suffix Rayleigh contracts for staged Lean implementation.

I checked `ORDERED_SPECTRAL_RAYLEIGH_PRE_REVIEW.md` at SHA-256 `16202cebdffbe6b094c9402a51038443e419b9a265cf156a650724ceaad691f2` against the frozen ordered PSD predicate, the existing exact double-sum spectral quadratic theorem, and the unchanged RA-10 source. All source hashes match. An `n×n` real matrix with orthonormal columns is a complete basis, so Parseval holds for the supplied Q without choosing a new basis. The already proved spectral expansion uses exactly the frozen double sum and the same coordinates `Σ_i x_i Q_i,b`.

If all coordinates with `b>a` vanish, the remaining eigenvalues are at least `eigenvalues a` by antitonicity, giving the proposed lower bound with coefficient one. If all coordinates with `b<a` vanish, the remaining eigenvalues are at most `eigenvalues a`, giving the proposed upper bound. The strict cutoffs are correctly oriented for the first-`a+1` and tail-from-`a` spans. Zero vectors, ties, zero eigenvalues, and empty dimension are covered without a positive-eigenvalue or normalization premise.

Approval covers these three exact generic signatures, with Parseval allowed as a separate first stage. Each implementation requires a frozen source hash, pinned LeanCert kernel check, and independent imported exact-signature/source/axiom audit before aggregate import. The nonzero intersection and compression eigenvalue comparison, nuclear inequalities, Lemma 2, integral transfer, and full RA-10 Target remain open.
