# SP-14 actual base-jet Fourier matrix: independent pre-proof review

**Verdict: approved after the cutoff wording correction.** The frozen theorem signatures describe coefficients of the actual interval-integral Fourier definition and the actual Toeplitz parity blocks. This is approval of the mathematical contract before Lean implementation, not a source/kernel audit or a proof of SP-14 Target.

## Frozen sources

| Source | SHA-256 |
| --- | --- |
| Reviewed revised `BASE_JET_FOURIER_MATRIX_PRE_REVIEW.md` | `fdb3b1ffc3daa48c80a49c03bc86777d865012eedff16b747414c3e45ffc1cbb` |
| Canonical `eigenvalues-and-inverse-problems/SP-14/README.md` | `9d0c6376080838ea50e8736cb4249276c06a528479fb9c9f565cc7747a485075` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BaseExteriorPattern.lean` / `NegativeRestorationInvisibility.lean` | `daf64cfcc02a7dd2aeab59403d1216046006daef2c7c7a987ac79ef22c40cdf4` / `318f9d1b2a0af4bf8355aa78afc7440b9c83449b6b2f5de8bd1bc361ac36e476` |
| `OddFrequencyToeplitzCharpoly.lean` / `BaseCB.lean` | `aa6de57a4b247b81296d36fb2ed70f47d9c0b1863d0290792f6f3c16b3d4aff5` / `4d08f355b18258aaee4a2a2a7c7546ffee8b13c81d746a8582aea105c7509e79` |

## Exact coefficient and matrix checks

The frozen convention is `FourierCoefficient a k=(1/2π)∫a(e^{it})e^{-ikt}dt` and `Toeplitzᵢⱼ=â(i−j)`. The exterior base has mode `1−2r` with coefficient `c_r=binom(1/2,r)`. The raw term `z negativeL(m,q,v)(z²)` has mode `1+2(d−m)=1−2(m−d)` with coefficient `v_d`. The restoration term `−negativeL(m,q,v)(−1) · z K_m(z²)` has modes `1−2(m+1+r)`, `0≤r≤m`, and coefficient `−negativeL(m,q,v)(−1)·restoringCoeff(m,r)`. Thus for every integer `p` the three contributions are precisely the base term, the `p=m−d` raw sum, and this restoration sum at `p=m+1+r`. Restricting to `p≤m` removes only the restoration sum and gives the contract's exact selected coefficient formula, including every negative `p`.

The condition `2q≤m+1` implies `d<m` for each `d:Fin q` when `q>0`; hence `m−d≥1` and the correction in `baseJetG` is a strict upper diagonal. For `oddBᵢⱼ`, row-minus-column frequency is `2i−(2j+1)=1−2((j+1)−i)`; for `oddCᵢⱼ`, it is `(2i+1)−2j=1−2(j−i)`. Both parameters range from `1−m` through `m`, so the selected coefficient theorem covers every entry. The raw condition `p=m−d` is exactly `j=i+(m−d)` in the selected `baseJetG`; for `p<0`, the base coefficient and strict upper-diagonal correction both vanish. This proves the specified `oddB`/`oddC` orientations without conjugation or a surrogate Fourier definition.

All component modes are odd, so the requested `OddFourierSupport` holds at every even integer frequency. The exterior series is continuous and both packets are finite circle-mode sums, providing the continuity needed for linearity of the frozen interval integral. The revised contract correctly limits its uniform restoration-free assertion to `p≤m`: restoration **may** contribute only for `m+1≤p≤2m+1`, and it vanishes entirely when `q=0` or `negativeL m q v (−1)=0`.

At `m=0`, `2q≤1` forces `q=0`: the selected blocks are empty in one dimension, while the coefficient formula still covers all `p≤0`. At `q=0` for any `m`, the actual symbol and matrix reduce to the base ones. At `m=1,q=1`, the raw coefficient adds `v₀` at `p=1` (`G₀₁`); restoration first appears at `p=2`, circle frequency `−3`, below the lowest diagonal frequency `−2` of `T₃`. The theorem does not assume a Fourier pattern for the corrected symbol; it demands proof from the frozen integral and reviewed mode orthogonality. It supplies only the matrix bridge for later finite cofactor and jet arguments; it proves no real right inverse, perturbed stage, or negative Target.
