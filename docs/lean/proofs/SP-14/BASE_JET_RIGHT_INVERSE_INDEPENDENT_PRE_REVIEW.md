# SP-14 base jet right inverse: independent pre-proof review

**Verdict: approved as an exact finite base-model contract.** This approves the mathematical specification before implementation, not a Lean proof or the final SP-14 counterexample.

## Frozen sources

| Source | SHA-256 |
| --- | --- |
| `BASE_JET_RIGHT_INVERSE_PRE_REVIEW.md` | `bbcb1bfe929f05bfdfe1a34e5e34b8d021b2aff365c8c60e7ec4900a16f1ee4d` |
| Canonical `eigenvalues-and-inverse-problems/SP-14/README.md` | `9d0c6376080838ea50e8736cb4249276c06a528479fb9c9f565cc7747a485075` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BaseCoefficient.lean` / `BaseCB.lean` | `63dcd98bb3a45e77b2b0fd2644d444f9cfe866fb9dae5535d1b7cd1f73081bf4` / `4d08f355b18258aaee4a2a2a7c7546ffee8b13c81d746a8582aea105c7509e79` |
| `BaseExteriorPattern.lean` / `NegativeRestorationInvisibility.lean` | `daf64cfcc02a7dd2aeab59403d1216046006daef2c7c7a987ac79ef22c40cdf4` / `318f9d1b2a0af4bf8355aa78afc7440b9c83449b6b2f5de8bd1bc361ac36e476` |
| `OddFrequencyToeplitzCharpoly.lean` | `aa6de57a4b247b81296d36fb2ed70f47d9c0b1863d0290792f6f3c16b3d4aff5` |

## Mathematical checks

- The frozen integral has row-minus-column Fourier indexing. The exterior base has modes `1−2r` with coefficient `c_r = binom(1/2,r)`; the raw correction `s^{d-m}` has circle mode `1+2(d−m)`. Hence the source's perturbation column `q_source=m−d−1` gives exactly `J⁰[k,d]=−2(k+1)c_{d−k}` for `k≤d`. The proposed complex polynomial and real matrix use the same orientation and coefficient normalization.
- For `E=∑_{d<q}v_d U^{m-d}`, the least nonzero shift is `m−q+1`; `2q≤m+1` implies `2(m−q+1)≥m+1`, so `E²=0` in size `m+1`. Since `G₀²=I+U`, `H=I+2G₀E`. All matrices are polynomials in `U`; therefore the proposed finite inverse is exact. In its upper-right entry, the coefficient of `t^k` is `−2(k+1)∑_{d≥k}c_{d−k}v_d`, because there are `k+1` placements of `k` factors of `tU` around `G₀E`. The unperturbed term is `t^m`. Thus the displayed `P_{m,q,v}` and the difference law are correct for every allowed `m,q`.
- The restored `K_m` packet alone has modes at most `−(2m+1)`, below the `2m+1` section's lowest diagonal frequency `−2m`. The existing theorem `toeplitz_add_restoration_invisible` supplies the needed actual-Toeplitz bridge with a continuous background; the exterior base and finite raw packet are continuous. The **full** restored packet is visible at the current section. The contract correctly requires a separate exact finite determinant/corner identity to identify `P` with the frozen `oddJetPolynomial = charpoly(oddC*oddB).comp (X+1)`; it does not infer that identity merely from a formal matrix surrogate.
- The real matrix is upper triangular with diagonal `−2(k+1)c₀=−2(k+1)`, so its determinant is nonzero for every `h`, including the empty case. Back substitution gives a real linear right inverse. Zero-padding to `Fin q` leaves the first `h` jets unchanged; the equality of first jets also proves the stated exact affine difference law and Jacobian rank `h` at every real vector. The `Ring.choose` coefficients over `ℝ` cast to the frozen complex `baseCoeff`.
- Endpoints are sound: `m=0` forces `q=h=0` and `P=1`; `q=0` gives `P=t^m`; `h=0` gives an empty invertible matrix. The specified examples yield `P=t−2v₀` at `(m,q)=(1,1)` and `P=t³−2v₀−v₁−4v₁t`, `J⁰=[[-2,-1],[0,-4]]` at `(3,2)`. I independently formed the rational Toeplitz sections from their actual Fourier modes and checked `det(wI−T)=wP(w²−1)` at `w∈{−2,−1,0,1,2}` for the empty vector at `(0,0)` and nonzero rational vectors at `(1,1),(2,1),(3,2)`; all 20 equalities hold.

The contract keeps the source's later `θ=2^-10000`, `q=3m/8`, `h=⌊θm⌋`, eight-divisibility and stage separation as a **separate all-background theorem**. This finite base right inverse does not establish its perturbed-background existence, weighted norm budgets, nonextension, or the frozen negative `Target`. The proposed proof must preserve the actual `FourierCoefficient`/`Toeplitz` bridge and the explicit restored symbol; replacing either by an abstract model would fall outside this approval.
