# RE-06 independent pre-implementation specification review

**Verdict: APPROVE.** I independently compared `NUMERICAL_TARGETS.md` with the complete canonical RE-06 page and the authored `solution.tex`. This approves the exact mathematical and operational specification before Lean implementation; it does not certify the proof or any future Lean machine semantics.

## Inputs and hashes

Published base: `0e916df335209819b5bf9bb8ed8f65ea978c049d`. SHA-256:

| Input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RE-06/README.md` | `df967515f033afaf9db8e77f5be522daf868817d7ee2951bed5b0e757696cbcf` |
| `docs/lean/statements/RE-06/ORIGINAL.md` | `df967515f033afaf9db8e77f5be522daf868817d7ee2951bed5b0e757696cbcf` |
| `docs/lean/statements/RE-06/NUMERICAL_TARGETS.md` | `ed37af5809b15afd1f9b4411356eaba15fceb9d988f41b0c7a5cda9089044865` |
| `randomized-and-low-rank-approximation/RE-06/solution.tex` | `8d875d2ef00fa3c777bc1b1ed6c527465e5038480cd991ce346b1d24df89d23d` |

`ORIGINAL.md` is byte-for-byte identical to the canonical README.

## Mathematical and numerical comparison

The specification retains all positive matrix orders, every explicitly given finite family of at least two distinct real square matrices, and an arbitrary fixed unknown real matrix with no norm, rank, conditioning, or membership premise. It uses the exact Frobenius objective with a finite attained minimum. Every execution returns a family member, and the inclusive `99/100` event is precisely `‖A−B‖_F≤(3+ε)OPT` for each fixed input. The `OPT=0` consequence, namely exact return of `A`, is correctly called out.

The query model permits **either** `Av` or `Aᵀv` for each real vector and charges each call, including repeated or zero vectors. The complete list of query vectors **and sides** is committed before any answer, although its plan may use the explicit family, `ε`, and randomness. Postprocessing may use the stored answers and the exact-real primitives, with no additional oracle call. This matches the canonical nonadaptivity requirement and the source's prequeried right and left Gaussian blocks. Conditioning on the first block during proof analysis does not authorize adaptive queries.

The original bound places one absolute `C>0`, nonnegative **integer** exponent `b`, and one uniform randomized algorithm before all inputs. The capped schedule length is at most `C sqrt(log(2M)) ε^(−2) [1+log(2+log(2M))+log(1/ε)]^b`, with natural logarithms. The same algorithm and plan must attain the `3+ε` guarantee with probability at least `99/100` for every fixed family, matrix, and `ε∈(0,1/2)`. The cap is worst-case over randomized plans; candidate and answer processing are not counted as queries. The source's stronger witness `4,000,000 sqrt(log(2M)) ε^(−2)` with `b=0` is accurately separated as a companion target. Its proved failure expression `e^(−8)+2e^(−16)+1/128+1/524288 < 0.008151` supports the stated stronger probability note. The `min(n,N)` exact-recovery branch, rank-deficient paths, and finite tie-breaking are reflected without becoming extra input assumptions.

The exact-real arithmetic, Gaussian, comparison, and SVD primitives agree with the canonical model. The specification correctly avoids adding bit complexity, floating-point stability, total runtime, streaming-memory, or an infinite-family claim. No material mathematical or numerical mismatch was found.

**Implementation gate:** The eventual Lean boundary needs a concrete uniform two-phase program/query semantics. An arbitrary function of the hidden matrix, an unconstrained `RunsInQueries` label, or a postprocessing oracle would invalidate this approval. Independently review those definitions and their imports after implementation.
