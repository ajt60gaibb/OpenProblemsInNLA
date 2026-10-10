# RA-10 noncommutative ridge-resolvent product: independent pre-review

**Author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact product gate for Lean implementation.

I reviewed `RIDGE_RESOLVENT_PRODUCT_PRE_REVIEW.md` at SHA-256 `82d171b76813e1c60ff8d00c2f2073167dadffbb8c1f7774f58584c03580ea2c` against the locked RA-10 solution, especially Lemma 2 and Equation (14), and the frozen `FunctionMatrix`. For every `s>0`, nonnegative supplied spectral values make each `s+aᵢ` nonzero. The shifted matrix has the explicit right inverse already kernel proved in `spectralShift_inverse`; square-matrix algebra gives `IsUnit` even for singular `A`, tied/zero eigenvalues, and dimension zero.

Writing `X=sI+A`, `Y=sI+C`, `R_A=X⁻¹`, and `R_C=Y⁻¹`, multiplication gives both exact orders `R_A(C−A)R_C=R_A−R_C` and `R_C(C−A)R_A=R_A−R_C`. Neither step commutes `A` with `C`. Multiplying by the literal positive scalar `s` matches the already audited identity `f_s(C)−f_s(A)=s(R_A−R_C)`. Substituting source `A=C_source`, `C=B₀_source` into the **second** order gives exactly the printed Equation (14) order `s(sI+B₀)⁻¹(B₀−C)(sI+C)⁻¹`, including sign and factors. The proposed public signatures keep the complete supplied decompositions and original frozen functional calculus.

Approval covers the shifted-unit theorem and both noncommutative product identities. Freeze any implementation for separate imported exact-signature and LeanCert kernel/axiom review. No nuclear ideal inequality, positive-part compression estimate, integral representation, or full RA-10 Target is credited by this review.
