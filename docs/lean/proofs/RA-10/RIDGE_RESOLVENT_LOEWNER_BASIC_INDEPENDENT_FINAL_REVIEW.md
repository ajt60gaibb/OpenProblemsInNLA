# RA-10 basic resolvent Loewner bounds: independent final review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact basic factor gate; the selected factor and full RA-10 Target remain open.

The frozen source `RidgeResolventLoewner.lean` has SHA-256 `c06a186419efdc23cf27a63238134becc4f89e215649daa67b459bd72b159d06`. I checked it against the independently approved source-locked Loewner precontract and the frozen real-matrix `PositiveSemidefinite` predicate. Its first two public theorems prove `0≼(sI+A)⁻¹≼(1/s)I` for every supplied ordered PSD eigendecomposition and `s>0`, including symmetry and nonnegative quadratic forms. The proof uses the actual shifted inverse's exact supplied spectral coefficients `1/(s+a_i)` and the exact upper-difference coefficient `a_i/[s(s+a_i)]≥0`; it includes zero eigenvalues and dimension zero. The third public theorem constructs a genuine `j:Fin n` with `j.val+1=k` from the frozen `1≤k<n` range, avoiding modular indexing.

An independent imported audit at `/private/tmp/ra10-ridge-resolvent-loewner-independent-audit.lean`, SHA-256 `d5e71d7572cc049cc22c29277a1c01d230e4764341a476930d5fd11acaf6a5c9`, elaborated all three exact public signatures, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`. No proof escape or new axiom appears in the source.

The sharp selected `P(sI+B₀)⁻¹P` bound, operator-norm conversion, nuclear ideal inequality, compression Lemma 2, integral representation, and frozen RA-10 Target remain open.
