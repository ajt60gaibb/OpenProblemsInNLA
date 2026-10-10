# RA-10 ridge resolvent matrix: independent pre-implementation review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact resolvent bridge for Lean implementation.

I reviewed `RIDGE_RESOLVENT_MATRIX_PRE_REVIEW.md` at SHA-256 `55240833a50a8403c827e0da38610a81ab6b6102117999587ff8747c0c6158d2` against the locked RA-10 solution and frozen statement. For each supplied ordered PSD decomposition, all eigenvalues are nonnegative, so `s+eigenvalues a>0` when `s>0`. Orthonormality of the square supplied `Q` gives `QᵀQ=QQᵀ=I`. The diagonal spectral formula therefore makes the exact frozen reciprocal `FunctionMatrix` a two-sided inverse of `sI+A`, including zero eigenvalues, ties, and dimension zero. Its equality to the actual matrix inverse has no hidden positive-definiteness or basis-selection premise.

The scalar equation `x/(s+x)=1−s/(s+x)` gives `FunctionMatrix (ridgeAtom s)=I−s(sI+A)⁻¹`. Subtracting the two identities in the proposed `C−A` order yields exactly `s[(sI+A)⁻¹−(sI+C)⁻¹]`, the source's Lemma 2 orientation and literal factor. The two matrices may have different supplied eigenbases and need not commute. Later use at `C=PAP` still requires its own decomposition bridge; this contract does not provide one implicitly.

Approval covers the three proposed public identities, with exact `FunctionMatrix`, actual shifted inverse, `s>0`, and no weakened target. Freeze the implementation for separate imported exact-signature and LeanCert kernel/axiom audit. Ridge compression, nuclear estimates, integral representation, and the RA-10 Target remain open.
