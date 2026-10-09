# RE-05 independent pre-implementation specification review

**Verdict: APPROVE.** I did not author this specification. I compared it independently with the canonical README and the complete Colbrook source, including Theorem 2.1 and Proposition 5.1. This is statement review, not proof certification.

| Reviewed input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RE-05/README.md` | `e8958ad5574576a781613326cdc4ba125b4ee1c2a7f41c64e6adddda3a06772b` |
| `docs/lean/statements/RE-05/ORIGINAL.md` | `e8958ad5574576a781613326cdc4ba125b4ee1c2a7f41c64e6adddda3a06772b` |
| `docs/lean/statements/RE-05/NUMERICAL_TARGETS.md` | `df935cbeef31796a83b9db2bc9d6f10a6a300d2d57cd3d0525d83646865d42f7` |
| `references/colbrook-transfer-2026-09-11/manuscripts/05_linear_family_relative_sketch.tex` | `240abf9fbaa23e7847b0ed5b80bea6fafc453969d826b0e3d60f6c580e151d57` |

The canonical README and retained `ORIGINAL.md` are byte identical. The specification keeps every `n≥1`, `1≤q≤n²`, independent real `n×n` basis, arbitrary fixed target `A`, and `0<ε<1/2`. It requires an output of **all** `q` coefficients and uses the exact attained Frobenius-distance minimum over the entire real span. The probability is at least `99/100` for every fixed admissible input, including `OPT=0` where exact recovery is necessary; no additive term or conditioning promise appears.

The query model includes both `Av` and `Aᵀv`, each charged once, with no direct read of `A`. The original allows adaptivity and imposes only a worst-case query cap, so the specification correctly treats the source's nonadaptive construction as a stronger witness rather than a new restriction. The allowed exact-real arithmetic, comparisons, Gaussian draws and exact SVD match the canonical context; no bit-cost or finite-precision claim is added.

The constants and exponents have the correct order: one uniform algorithm and absolute `C>0`, `a,b∈ℕ` precede all inputs and randomness; every run obeys the displayed `C√q ε^(−a)[1+log(2+q)+log(1/ε)]^b` bound. The 15-copy source amplification uses squared excess `ε/9`, yields failure at most `e^(−4.8)<0.01`, and converts the squared-distance theorem into the required norm factor at most `1+ε`. The specification keeps these as source witness details without replacing the full canonical `99/100` target. No mismatch requiring revision was found.
