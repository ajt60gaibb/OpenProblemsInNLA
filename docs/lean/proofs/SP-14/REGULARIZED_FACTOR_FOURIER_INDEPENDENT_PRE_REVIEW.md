# SP-14 regularized exterior factor Fourier series: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen narrow addendum for implementation. This approves the exact circle series and frozen Fourier coefficients, not the bilateral Wiener norm or negative Target.

| Reviewed input | SHA-256 |
| --- | --- |
| `REGULARIZED_FACTOR_FOURIER_PRE_REVIEW.md` | `6cc17eebf8c7664f6945a0405e4755c5cfaac2d2d023562968ca79a4ccf4f119` |
| Parent endpoint-Wiener contract | `6bd5adcd58819b4ad585bb25fd565ee33453c51c341e58e1ccf136a6cbfe9175` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Audited boundary factor | `a8dbc23e8544378ab504ff8130387701fa0270cb2753555c0f05b71057d316dd` |
| Audited regularized coefficients | `09aac1a792bbfaf481c94ff2ff2f294bb2ea451afe87d2b3aa9199b34cac4aa6` |

The proposed `regularizedBaseFactor` is the actual pointwise product `(1+s)g₀(s)`. Multiplying the absolutely convergent series `Σ_n c_n s^(−n)` by `1+s` gives one term `c₀s=s` at frequency `+1`, and for frequency `−n` gives exactly `c_n+c_(n+1)=d_n`. In particular `F₁=1`, `F₀=d₀=3/2`, `F_(−1)=d₁=3/8`, and `F_(−2)=d₂=−1/16`; all frequencies `k≥2` vanish. The proposed `if k=1 … else if k≤0 …` signature is disjoint and uses `k.natAbs=n` precisely when `k=−n`. Contact at `s=-1` follows from the actual product, without division by the boundary zero.

The frozen `FourierCoefficient` is the normalized real-interval integral with phase `e^(−ikt)`. The already audited pure-mode orthogonality and absolute coefficient summability justify termwise integration of the regularized series, so the claimed all-integer theorem refers to the actual integral rather than a merely formal coefficient field. Continuity follows from the reviewed base factor and pointwise multiplication. The source's `9/8` coefficient summability belongs to the previous gate and will support a later Wiener norm; this gate makes no norm or full-target claim.

Implementation must preserve the exact source integral, complex `Circle` powers and frequency signs, including `k=0`, all negative `k`, and positive `k≥2`. Its source should remain unimported until a separate LeanCert kernel/signature audit. Endpoint division, weighted convolution and all other smallness conditions remain open.
