# RA-10 ridge resolvent matrix identities: independent final review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact resolvent gate; the compression inequality and full RA-10 Target remain open.

The frozen source `RidgeResolventMatrix.lean` has SHA-256 `1523abd991863c75f890cac0abfcc905948716a0179e05985f16fdf6fed233c8`. I checked it against the independently approved source-locked ridge-resolvent contract and the frozen RA-10 `FunctionMatrix`. Its first public theorem proves, for every supplied PSD eigendecomposition and `s>0`, the exact matrix identity `FunctionMatrix (ridgeAtom s) eigenvalues Q = I − s • (sI+A)⁻¹`. It uses the scalar equality `x/(s+x)=1−s/(s+x)` only at the nonnegative supplied eigenvalues, and the constant spectral matrix is exactly `I` because the same supplied square `Q` is orthonormal. The second theorem subtracts two such identities with independent supplied bases and yields the source's exact orientation `f_s(C)−f_s(A)=s[(sI+A)⁻¹−(sI+C)⁻¹]`. No commutation, nonsingularity of `A` or `C`, or basis choice is added.

An independent imported audit at `/private/tmp/ra10-ridge-resolvent-matrix-independent-audit.lean`, SHA-256 `fbcc48a7b9cecad986820f5563a20f3e820853dec52e525eff3e24b8cc2d81f8`, elaborated both exact public signatures, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`. No proof escape or new axiom appears in the source.

This algebra does not prove the matrix ridge compression estimate, nuclear pinching, the positive-integral transfer, or the frozen RA-10 Target.
