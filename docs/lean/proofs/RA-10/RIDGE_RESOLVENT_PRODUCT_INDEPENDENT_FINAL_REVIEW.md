# RA-10 noncommutative ridge-resolvent products: independent final review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact product gate; the matrix compression estimate and full RA-10 Target remain open.

The frozen source `RidgeResolventProduct.lean` has SHA-256 `0e608459592be87ecbcd06d4e787b167352ef593392334447ce2aba237cc70b2`. I checked it against the independently approved product precontract, the locked solution's Lemma 2 and Equation (14), and the frozen ridge `FunctionMatrix`. The first public theorem proves the actual `sI+A` is a unit for every supplied ordered PSD decomposition and `s>0`, including singular `A`, tied/zero eigenvalues, and dimension zero. It explicitly factors the shifted matrix as `Q diag(s+a) Qᵀ`, with each scalar nonzero. The other public theorems prove both exact noncommutative orders for `f_s(C)−f_s(A)`: `s R_A(C−A)R_C` and `s R_C(C−A)R_A`, with independently supplied bases and no commutation assumption. The second order specializes to source Equation (14) with its printed sign and factor.

An independent imported audit at `/private/tmp/ra10-ridge-resolvent-product-independent-audit.lean`, SHA-256 `15f0c97238089e25a4744dfcf9e4059114b245c4312ddf1ed75cda5302236d46`, elaborated all three exact signatures, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`. No proof escape or new axiom appears in the source.

This finite matrix algebra does not prove the nuclear ideal inequality, positive-part ridge compression, operator-monotone integral representation, or the frozen RA-10 Target.
