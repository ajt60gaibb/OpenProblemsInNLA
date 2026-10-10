# MF-03 all-complex cosine product: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import. It proves the exact positive-factor product identity and convergence of its finite products for every complex argument. It does not prove the Padé denominator coefficient bounds or full MF-03 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/CosineAllComplexProduct.lean` | `59b6a9cf45df57ae13933abf6aecbbcce47f8c63269f8219b9dcd7cdbd016dbc` |
| Exact pre-implementation contract | `18e82a78f3c77a1cbc6c7d55f0c437cb44832cdd04698c287d402cf942695fcc` |
| Independent mathematical pre-review | `603afea5884478158665bfa930ad5aff09e087759c0d9e9c9681a43fffbee10f` |
| Separate imported audit `/private/tmp/mf03-cosine-allcomplex-independent-audit.lean` | `144fb758f92789f3f37de7a41afda192d162e9810b6cc6da08cdf51abc736322` |

The source uses the exact factors `1+a_kz` with `a_k=1/[π²(k+1/2)²]`, indexed from `k=0`. Around any `z₀`, the summable sequence `(‖z₀‖+1)a_k` dominates all factor perturbations in a neighborhood. The pinned dominated-convergence theorem for infinite products proves continuity, including product zeros. The complex sine-zero set of `sin(πw)` is exactly the integer casts; its complement is dense. The audited dense-set finite-product limit and the product's `HasProd` limit are limits of the same sequence, so continuity extends their equality to every `w`.

Algebraic closedness makes `w↦−(πw)²` surjective over `ℂ`. Thus the public theorem is the reviewed `tprod` equality for **every** complex `z`, with no sine premise. The second public theorem identifies the limit of the exact finite products with the factorial `waveSeries` at every `z`. The printed imported signature elaborates `tprod (fun k : ℕ => ...)` to the approved `∏' (k : ℕ), ...` form; the factor indexing and value are identical.

The pinned Lean 4.33.1 direct module build passed 8,712 jobs. My separate imported LeanCert audit exited zero, checked both exact public signatures, reran both `#assert_trust kernel` checks, and printed only `[propext, Classical.choice, Quot.sound]` for each. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

Infinite-product coefficient transfer, Schur/tableau denominator bounds, all-order normalized pair existence, orders at least 16, and full MF-03 Target remain open.
