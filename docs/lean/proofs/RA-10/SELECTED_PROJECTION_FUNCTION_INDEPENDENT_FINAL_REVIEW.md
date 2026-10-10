# RA-10 supported functional calculus: independent final review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this exact partial gate; the full RA-10 Target remains open.

The frozen source `SelectedProjectionFunction.lean` has SHA-256 `78b15a4bcdcbbd0bebb87a6f64a8e99db062ecdd5d85a125b04be99b45b29dee`. I checked it against the independently approved selected-projector precontract and the frozen RA-10 `FunctionMatrix` and `FunctionTruncation`. Its public theorem states, for every supplied ordered PSD spectral decomposition and every real function `f`, the exact matrix identity `selectedProjection k Q * FunctionMatrix f eigenvalues Q * selectedProjection k Q = FunctionTruncation k f eigenvalues Q`. It uses the same supplied `Q`, strict zero-based cutoff `a.val<k`, and no eigenvalue gap or assumption `f 0 = 0`.

The proof expands the literal spectral sums as `Q` times diagonal matrices times `Qᵀ`, uses precisely the frozen column orthonormality equation `QᵀQ=I`, and computes the selected diagonal product. It remains valid for tied eigenvalues, selected zero eigenvalues, `k=0`, and `k>n`. An independent imported audit at `/private/tmp/ra10-selected-function-independent-audit.lean`, SHA-256 `8095245a6aefbd03471bd5cf7483c2c2497a88d0f546de4fd5748165e51a4cd1`, elaborated the exact public signature, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`. No proof escape or new axiom appears in the source.

This identity does not prove nuclear-norm pinching, ridge compression, the general integral representation, the literal constant-eleven transfer, or the frozen RA-10 Target.
