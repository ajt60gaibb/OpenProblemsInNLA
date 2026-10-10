# RA-10 selected resolvent Euclidean operator norm: independent final review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact selected factor; the nuclear ideal inequality and frozen RA-10 Target remain open.

The frozen source `RidgeResolventOpNormSelected.lean` has SHA-256 `845a5cdcc7eb79f87a76e66cdb4614207b82b74f1fb8bb4137e7806a6c8a18ef`. I checked it against the independently approved source-locked Euclidean operator-norm contract and RA-10 source Equation (14). Its scoped `Matrix.Norms.L2Operator` instance makes the displayed norm the Euclidean induced operator norm. The theorem uses the actual `P=selectedProjection k QAhat`, matched leading matrix `B₀=FunctionTruncation k id eigenvaluesA QAhat`, and supplied `QAhat` basis. Its diagonal coefficients are `1/(s+a_i)` for zero-based indices `i<k` and zero outside. The witness `j.val+1=k` gives exactly one-based `c=a_k`; supplied eigenvalue order yields the sharp `1/(s+c)` bound. It does not claim that bound for the full inverse, whose complementary eigenvalue is `1/s`, or require `QA=QAhat` or commutation with `C`. Ties and zero selected eigenvalues are retained.

An independent imported audit at `/private/tmp/ra10-selected-resolvent-opnorm-independent-audit.lean`, SHA-256 `f9c74699affd0e633ac5766da223ea48ee3806cd2ff8e5dc8532b6a80c412eb4`, elaborated the exact public signature under the same scoped norm, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`.

Support insertion into the unsandwiched Equation (14) product, the nuclear ideal-property inequality, compression Lemma 2, integral transfer, and the full RA-10 `Target` remain open.
