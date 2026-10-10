# TR-14 local Fourier symmetric upper bound: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen narrow contract as the exact local-interpolation construction in canonical `solution.tex` §3. This is a pre-implementation review, not a proof of a symmetric width or of the frozen all-width `Target`.

| Reviewed input | SHA-256 |
| --- | --- |
| `LOCAL_FOURIER_UPPER_PRE_REVIEW.md` | `7466b599503bcca7dbe9f99e784acdf2b0a2569b80b7f1c4baf1dcd148b87351` |
| Canonical `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |

I checked the source's conditional moment-algebra route against the contract: a nonzero least homogeneous apolar form is moved by an invertible chart to a monic degree-`r₀` polynomial without deleting projective roots or changing their multiplicities. The audited quotient and Frobenius lemmas provide the all-moment functional and nondegenerate pairing needed for the local CRT restrictions. The local top-coefficient representation has `u_j=λ_a(z^(ℓ−1−j))`; in particular `u_0≠0` follows from Frobenius nondegeneracy because `z^(ℓ−1)` annihilates every positive-degree class. A finite binomial root then gives `w^m=u` in the nilpotent local ring. The contract requires these as proofs from `h`, not extra premises of `Target`.

For `N=(m−1)(ℓ−1)+1`, the product of `m` degree-`<ℓ` representatives has degree at most `m(ℓ−1)`. Its selected degree is `ℓ−1`; the next congruent degree is `m(ℓ−1)+1`, above the maximum, and the previous is negative. Hence root-of-unity filtering returns exactly that coefficient with factor `N⁻¹ζ^(−(ℓ−1))`. At `ℓ=1`, `N=1` and the sole degree and node are zero and one respectively. No binomial coefficient enters the zero-based mode polynomial `Σ_i v_i t^i`, and evaluation is correctly applied to each unique polynomial representative, not to an abstract quotient class at a nonnilpotent root of unity.

The local factors produce the same coordinate vector in every tensor mode. With `s` distinct roots and `Σ_aℓ_a=r₀`, their exact count is `Σ_aN_a=(m−1)r₀−(m−2)s`. The displayed equality is the frozen `SymmetricWidth` coordinate equation at that width. Its reverse chart transport covers the original root-at-infinity case. The zero tensor remains a separate width-zero case, and the balanced least-kernel case does not require uniqueness of the chosen apolar form. The construction is valid when `r₀>n` because local polynomial reduction is independent of mode dimension.

Implementation may split CRT, local algebra, Fourier filtering, moment bridge, and coordinate decomposition into modules. Each exact signature must be checked against this contract before coding and independently audited after freezing. The second symmetric upper construction and the arbitrary ordinary lower bound remain open; this approval does not infer the full exact-rank formula.
