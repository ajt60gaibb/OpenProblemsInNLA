# TR-14 affine dehomogenization and chart selection: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import as a partial chart-normalization result. The monic scaling package and the frozen all-width target remain open.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/GL2Dehomogenize.lean` | `3de97ab8ba4f9733fe6e876808f9d6ea9c0e1d33ff9ddea9219baf09aeda9af5` |
| Chart-normalization mathematical contract | `8d1c179386d1631fbdbd231db4a9b9b9db5d85043ad405fe24d2a3afadcf76e7` |
| Independent preimplementation review | `47bad244d52518460cb481cf9e02ed17628cc3c1b702b3002fb0411878c9559e` |
| Audited `GL2ApolarTransport.lean` | `8e75a3257801d3738bb0dad87a4dbdab5a614e84449c6874b6f6ac418d814c3b` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separate imported audit `/private/tmp/tr14-gl2dehomogenize-independent-audit.lean` | `e9139f334adbf4db984fed4839c5d21db3c0cdfadd635171448cf825e53a548d` |

The source defines the affine polynomial by the exact finite coefficient map `Polynomial.ofFn (d+1)` and proves that its coefficient at every `i:Fin(d+1)` is `g i`; it is zero exactly when the whole vector is zero. It also gives the exact finite evaluation sum. These signatures cover `d=0`, trailing zero coefficients, and vectors whose original final coefficient vanishes.

The chart theorem uses the already audited homogeneous coefficient basis and explicit substitution `(X,Y)↦(Y,X+zY)`. A homogeneous degree-`d` form evaluated at `(0,1)` selects its final `Y^d` coefficient; the substituted form at `(0,1)` equals the original form at `(1,z)`. The proof checks this through the polynomial evaluation homomorphism, with no conjugation, binomial scaling, or reversed coefficient index. The exported identity is exactly `(transportedApolarVector z d g)_d = (dehomogenize d g).eval z`. Because the dehomogenized polynomial is nonzero for `g≠0` and `ℂ` is infinite, the exported existential theorem selects a chart with nonzero **last** transformed coefficient. It does not impose an initial monic chart or a nonzero original last coefficient.

The separate audit imported the compiled source using pinned Lean 4.33.1, checked all public signatures, reran `#assert_trust kernel`, and printed exactly `[propext, Classical.choice, Quot.sound]` for the five exported theorem types. It exited zero. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape.

This module does not yet scale the selected apolar form, prove the resulting polynomial monic with exact degree, preserve the least-degree premise, or transport any Hankel width. Those remain the next independently audited obligations. Changed source bytes require a new review.
