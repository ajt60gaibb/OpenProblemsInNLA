# MF-08 independent pre-implementation specification review

**Verdict: APPROVE.** I did not author this specification. I compared it independently with the complete canonical README, its original problem TeX, and the repository's actual binary-encoding and finite-machine complexity definitions. This is a statement-fidelity review, not a proof audit of either cited hardness preprint.

| Reviewed input | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-08/README.md` | `f1be500b7a835ccfdaf00db211fe71e27b0fed4108aaf979e4136c95fd656dfe` |
| `docs/lean/statements/MF-08/ORIGINAL.md` | `f1be500b7a835ccfdaf00db211fe71e27b0fed4108aaf979e4136c95fd656dfe` |
| `docs/lean/statements/MF-08/NUMERICAL_TARGETS.md` | `f39c5b22ee0a6689209b898c1aca8175ad567f1b574c62d0272b07820f8b64f7` |
| `matrix-functions-and-stability/MF-08/problem.tex` | `6f822d1063935bc56597b6d32ac4cca09b4c557b03dbc981763e0151186f2a56` |

`ORIGINAL.md` and the canonical README are byte identical. The ID and canonical path remain fixed.

The specified input is every positive-dimensional rational triple `A : n×n`, `B : n×m`, `C : p×n`. The proposed exact signed-rational, self-delimiting row-major encoding includes the dimension bits and all entries; rejecting malformed inputs and unchecked suffixes makes one fixed binary language. `NLA.Computation.BinaryEncoding` already provides canonical natural and rational components, including normalized denominator and sign; the proposed extension to three rectangular matrices preserves the source's bit-size model.

The yes condition quantifies an arbitrary real `K : m×p` and requires the **strict** inequality `λ.re < 0` for every complex eigenvalue of the actual finite-sum product `A+BKC`. The nonzero-complex-eigenvector formulation is equivalent to this finite-dimensional spectrum condition. It introduces no gain bound, sparsity restriction, chosen poles, or promise on the plant. The cited integer subclasses sit inside this rational language with denominator-one entries.

The target is `NLA.Computation.Complexity.ManyOneNPHard` of this exact language. That existing predicate quantifies actual finite transducer runs with uniform polynomial bit-time bounds and all source languages in `InNP`; it is the required polynomial-time many-one notion. The specification neither claims NP membership nor substitutes a heuristic or a weaker bounded-feedback problem. There is no numerical tolerance, probability or real-arithmetic cost hidden in the question. I found no mismatch requiring revision before Lean implementation.
