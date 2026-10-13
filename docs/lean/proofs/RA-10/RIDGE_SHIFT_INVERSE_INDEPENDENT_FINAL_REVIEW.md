# RA-10 shifted inverse: independent final review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact first resolvent gate; the ridge subtraction and full RA-10 Target remain open.

The frozen source `RidgeShiftInverse.lean` has SHA-256 `db487f99898c55bd9958b19b2cfdd576342a36fdb21ec7f6269954309bac77e0`. I checked it against the independently approved ridge-resolvent matrix precontract and frozen RA-10 spectral definitions. For every supplied ordered PSD decomposition and `s>0`, its public theorem identifies the frozen `FunctionMatrix (fun x => 1/(s+x)) eigenvalues Q` with the actual inverse of `sI+A`. The proof expands the literal spectral sums, derives `QᵀQ=I` and `QQᵀ=I` for the same supplied square `Q`, uses nonnegative eigenvalues to invert every `s+eigenvalues a`, establishes a right inverse, and invokes Mathlib's actual square-matrix inverse theorem. It covers singular `A`, ties, zero selected eigenvalues, and dimension zero without a positive-definiteness assumption on `A`.

An independent imported audit at `/private/tmp/ra10-ridge-shift-inverse-independent-audit.lean`, SHA-256 `85791ff98accd8f93fe589ecf0186af33afeb5729e049e461e94bea2ff977dd9`, elaborated the exact public signature, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`. No proof escape or new axiom appears in the source.

The literal ridge functional-calculus and subtraction identities, compression inequality, nuclear estimates, integral representation, and full RA-10 Target remain open.
