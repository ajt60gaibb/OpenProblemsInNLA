# SP-14 finite complex Fourier-matrix Schur bound: independent final review

**Source author:** `/root/sp14_base_proof`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this exact finite complex operator gate for aggregate import.

The exact source-locked contract `ENDPOINT_FINITE_MATRIX_SCHUR_PRE_REVIEW.md` is SHA-256 `d82718940026325258b9df63a58a014f6d29fa1794e2ce6d90a583941251980d` and was independently reviewed before implementation. The frozen source `lean-statements/NLA/Proofs/SP14/EndpointFiniteMatrixSchur.lean` is SHA-256 `0b8c3b6c2647a2f955a638993b0560343cc101f10adb8df16ad4fd096800de3b`.

I checked that each complex entry is definitionally `(t+1)^r(k+1)^(-r)` times the actual frozen `FourierCoefficient` of `endpointBaseSymbol·endpointInverseMonomial k` at negative frequency `−(t+1)`. Its norm is exactly the previously audited `endpointWeightedKernel r (t+1) k`. The public theorem is for every real `0<r<1`, every `J,N : ℕ`, and every `x : Fin N→ℂ`; it bounds the sum of squared complex row norms by exactly `endpointSchurConstant r ^ 2` times the squared input norm. The literal constant is `1+1/r+1/(1−r)`; the theorem permits `J=0`, `N=0`, `j=1`, and `k=0`. The proof uses the finite row/column inequalities, weighted Cauchy–Schwarz, and finite sum interchange; it does not replace the Fourier entries with an unrelated matrix or add a dimension factor.

The direct pinned Lean 4.33.1 module build passed. My separate imported exact-signature audit `/private/tmp/sp14-endpoint-finite-matrix-schur-independent-audit.lean` is SHA-256 `94761528d3f6f3bb2432ea7bd0505157f9113dbd2f72ea0dbb8e0e38b2419112`; it checked the exact Fourier-entry definition, norm identity, public all-size inequality and LeanCert `#assert_trust kernel`. Both axiom reports were exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no proof escape. Changed source bytes require a new review.

This finite theorem does not construct the infinite-dimensional endpoint extension, prove its total two-sided `H^r` bound, its inverse Hilbert–Schmidt estimate, endpoint vanishing, perturbed-background inverse, or frozen SP-14 negative `Target`.
