# TR-14 local top-coefficient algebra: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen exact local-algebra contract for staged implementation. It constructs no CRT, global local decomposition, symmetric width, or frozen Target proof.

| Reviewed input | SHA-256 |
| --- | --- |
| `LOCAL_TOP_COEFFICIENT_PRE_REVIEW.md` | `c5797947009882f77bacc12d3a3f641178a38a6aa134ffc842aba9cb9ecab37b` |
| Canonical `solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |

For `B_ℓ=ℂ[z]/(z^ℓ)` with `ℓ≥1`, the monic power basis is exactly `1,z,…,z^(ℓ−1)` and `z^ℓ=0`. The proposed coefficient rule is the complete truncated convolution at each degree `j<ℓ`; no term above degree `j` can contribute after reduction. Reversing the local functional values is correct: if `u_i=Λ(z^(ℓ−1−i))`, then the top coefficient of `u a` is `Σ_{j=0}^{ℓ−1}u_(ℓ−1−j)a_j=Σ_jΛ(z^j)a_j=Λ(a)`. Applying this equality to all basis elements also proves uniqueness. The constant coefficient is `u₀=Λ(z^(ℓ−1))` exactly.

If `u₀=0`, the nonzero class `z^(ℓ−1)` pairs to zero with every local class: multiplying it by `a` retains only `a₀ z^(ℓ−1)`. This contradicts the stated left-radical nondegeneracy and includes `ℓ=1`, where the class is one. Thus `u₀≠0`, and in the truncated polynomial algebra that condition makes `u` a unit. No nondegeneracy may be assumed without proof when the local functional is later obtained from the global quotient.

For every positive `m`, complex algebraic closedness supplies `ρ^m=u₀≠0`. At step `j≥1`, the degree-`j` coefficient of `(W_<j+w_j z^j)^m` is `R_j+mρ^(m−1)w_j`: two new degree-`j` terms have degree above `j`, while all other factors contribute their constants. The denominator is nonzero in characteristic zero, so the displayed exact recursion solves each coefficient through `ℓ−1`; equality in the power basis gives `w^m=u`. At `ℓ=1` there are no recursion steps; the `ℓ=2` and `m=3,ℓ=3` formulas in the contract agree with direct expansion. This is finite algebra, independent of analytic convergence.

The implementation may split representation and root existence into smaller modules, but must prove the power-basis and truncated multiplication facts before claiming the reversed-index formula. The local multiplicity may exceed the tensor mode dimension, and chart normalization handles infinity separately. CRT, transfer of the global Frobenius functional, the local Fourier summation over roots, both symmetric upper bounds, and the arbitrary ordinary lower bound remain open.
