# RE-05 pre-implementation specification: independent review

**Verdict: APPROVE.** Reviewer: `/root/inventory_review`, 2026-10-09. This checks the retained target against its source; it does not review a Lean implementation or re-prove the manuscript.

I compared the complete canonical README, its byte-identical `ORIGINAL.md` copy, the proposed specification, and Theorem 2.1 and Proposition 5.1 of the cited resolution. The specification keeps one uniform randomized algorithm for every positive `n`, `1≤q≤n²`, every linearly independent explicit real matrix family, every arbitrary target matrix accessed only through `Av` and `Aᵀv`, and every `0<ε<1/2`. It requires coefficient output in the actual span and pure **norm** relative error against the attained Frobenius minimum, including exact reconstruction on zero optimum. It retains the at-least-`99/100` success probability for each fixed input.

The exact-real arithmetic and query model matches the canonical statement: both oracle directions count one call, adaptation is permitted, and computation between calls is unrestricted. The specification gives the original worst-case call cap with one positive absolute `C` and natural exponents `a,b` chosen before all inputs and randomness. Its discussion of the source's nonadaptive constant-success method and fifteen-copy amplification is correctly labeled as a stronger route, not as a replacement for the target. I found no omitted quantifier or changed numerical threshold.

| Input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RE-05/README.md` | `e8958ad5574576a781613326cdc4ba125b4ee1c2a7f41c64e6adddda3a06772b` |
| `docs/lean/statements/RE-05/ORIGINAL.md` | `e8958ad5574576a781613326cdc4ba125b4ee1c2a7f41c64e6adddda3a06772b` |
| `docs/lean/statements/RE-05/NUMERICAL_TARGETS.md` | `df935cbeef31796a83b9db2bc9d6f10a6a300d2d57cd3d0525d83646865d42f7` |
| `references/colbrook-transfer-2026-09-11/manuscripts/05_linear_family_relative_sketch.tex` | `240abf9fbaa23e7847b0ed5b80bea6fafc453969d826b0e3d60f6c580e151d57` |
