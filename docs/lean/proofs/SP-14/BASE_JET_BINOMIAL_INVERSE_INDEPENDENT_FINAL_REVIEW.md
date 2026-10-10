# SP-14 explicit base-Jacobian binomial inverse: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import as a finite preconditioner component. It does not prove the actual-background Sobolev isomorphism or the SP-14 negative target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/BaseJetBinomialInverse.lean` | `362a891068b132248f388bf364908f6a7350fa3f7d226debfb658e3847db3e47` |
| Exact mathematical/numerical precontract | `2e56799ab554b33a04bf8c7ec8c8729095c4e8a21b82d2b0046781f3bc3476` |
| Independent preimplementation review | `2723ee9d844f3ba1f79a0124f6ac67a56a87e75cfa0aa85c2de37fa96ae533c3` |
| Audited `BaseJetTriangular.lean` | `a1cff804e204a656bed6f0b45d06d0d0e0f238d385468bcda4384b72cd790ccc` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Separate imported audit `/private/tmp/sp14-basejetbinomialinverse-independent-audit.lean` | `b523852e939ea74e0c6fe9a79297b6513cdea86d0d1d317ca39c9963e00ecfd3` |

The source defines the finite inverse entry in the reviewed row/column orientation: correction row `d`, output column `k`, value `−(1/2) binom(−1/2,k−d)/(k+1)` for `d≤k`, zero otherwise. The existing `baseJetMatrix` has output row `k`, correction column `d`, value `−2(k+1) binom(1/2,d−k)` for `k≤d`. These are the exact source coefficients and include the empty `Fin 0` case.

The public scalar convolution theorem obtains every coefficient of `(1+X)^(1/2)(1+X)^(−1/2)=1` from Mathlib's binomial power-series product. The proof of `N M=I` then reindexes the finite upper-triangular product into that convolution; no matrix inverse is assumed at this step. The previously audited nonsingularity of `M` identifies `N` with its genuine inverse, yielding `M N=I` and equality of `baseJetSolve q x` with the source's explicit `N.mulVec x` for all `q,x`. Thus both public products and the solve identity hold, rather than only a one-sided formal inverse. The independent pre-review's exact rational checks for `q=0..3` fix the signs and denominators.

The separate imported LeanCert audit exited zero in pinned Lean 4.33.1, checked both definitions and all four public theorem signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]` for each theorem. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The exact limiting Jacobian, conformal map, compatible Sobolev extensions and their `2^100` bounds, forcing, nonlinear construction, infinite symbol, nonextension, gap, and frozen negative `Target` remain open.
