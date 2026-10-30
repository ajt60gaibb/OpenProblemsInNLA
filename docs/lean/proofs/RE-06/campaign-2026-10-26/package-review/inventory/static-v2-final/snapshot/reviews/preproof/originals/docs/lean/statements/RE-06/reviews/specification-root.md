# RE-06 independent specification review

**Verdict: APPROVE** for Lean statement implementation. The specification
author is `/root/fr05_review`; I compared it independently with the
canonical target and complete resolution source. This does not verify a
future Lean program or the mathematical proof.

## Bound inputs

Published base: `0e916df335209819b5bf9bb8ed8f65ea978c049d`.

| Input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RE-06/README.md` | `df967515f033afaf9db8e77f5be522daf868817d7ee2951bed5b0e757696cbcf` |
| `docs/lean/statements/RE-06/ORIGINAL.md` | `df967515f033afaf9db8e77f5be522daf868817d7ee2951bed5b0e757696cbcf` |
| `docs/lean/statements/RE-06/NUMERICAL_TARGETS.md` | `ed37af5809b15afd1f9b4411356eaba15fceb9d988f41b0c7a5cda9089044865` |
| `randomized-and-low-rank-approximation/RE-06/solution.tex` | `8d875d2ef00fa3c777bc1b1ed6c527465e5038480cd991ce346b1d24df89d23d` |

The original copy matches the canonical README byte for byte. Source
Theorem 1.1 and Sections 2–6 confirm the fully nonadaptive query model,
`3+ε` finite-family approximation, exact-real arithmetic convention and
numerical query/probability bounds.

The specification retains every positive dimension, every explicitly
given finite family of at least two distinct real square matrices, every
fixed unrestricted unknown real matrix, and every `0<ε<1/2`. It makes
both right and transpose query vectors and **query sides** part of a
precommitted plan before any oracle answer; postprocessing cannot request
more products. Only these products are charged. The exact-real Gaussian,
comparison and SVD primitives are permitted, without inserting a
finite-precision or total-work guarantee.

The output belongs to the finite family, and one event of probability at
least `99/100` gives `‖A−B‖_F≤(3+ε)OPT`, with `OPT` the attained minimum
over the whole family. For `OPT=0` the event forces exact recovery.
The original existential `C>0,b∈ℕ` worst-case query rate and the stronger
source witness `C=4,000,000,b=0` are separate assertions. Source lines
96–105 and 517–526 confirm the constants and nonadaptivity; the stronger
`1−0.008151` success lower bound is optional. No assumption of full-rank
sketches, positive optimum, or family membership of `A` is added. I found
no substantive mismatch. The Lean operational semantics and all imports
still require independent boundary review.
