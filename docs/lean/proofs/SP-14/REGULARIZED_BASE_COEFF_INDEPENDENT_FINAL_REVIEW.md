# SP-14 regularized exterior coefficients: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen first endpoint-Wiener source for aggregate import. It proves exact cancellation coefficients and their `9/8`-weighted summability, not the full product norm or negative Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/RegularizedBaseCoeff.lean` | `09aac1a792bbfaf481c94ff2ff2f294bb2ea451afe87d2b3aa9199b34cac4aa6` |
| Revised exact endpoint-Wiener contract | `6bd5adcd58819b4ad585bb25fd565ee33453c51c341e58e1ccf136a6cbfe9175` |
| Independent mathematical pre-review | `e12a9aa5436a67b0d9a42f1944b24064d374a229386d2f3a7e628082484bc08f` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Separate imported audit `/private/tmp/sp14-regularizedbasecoeff-independent-audit.lean` | `b5b879b20f4b87b8ff4bb2e437d202054b24c6cf39305100f9d96ff33de4a425` |

The source defines `d_n=c_n+c_(n+1)` from the audited half-binomial coefficients and proves `(n+1)d_n=(3/2)c_n` for every `n≥0`, including zero. Exact rational proofs give `d_0=3/2`, `d_1=3/8`, and `d_2=−1/16`, matching direct coefficient arithmetic. The `n≥1` absolute-value recurrence yields a decreasing cubic-weighted squared majorant `(n+1)^3‖c_n‖²≤2`; the source checks `n=0` and `n=1` separately. Consequently `‖c_n‖≤2(n+1)^(-3/2)` and the exact cancellation recurrence gives `(n+1)^(9/8)‖d_n‖≤3(n+1)^(-11/8)`. The right side is summable by the pinned real p-series theorem since `11/8>1`, proving the proposed unconditional weighted summability. No floating-point approximation is used.

The pinned Lean 4.33.1 direct module build passed 2,623 jobs. My separate imported LeanCert audit exited zero, checked all public signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]` for the recurrence and weighted summability. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The actual circle factor `F=(1+s)g₀` Fourier identification, finite endpoint division, the bilateral weighted convolution bound, the other four smallness inequalities, compatible Sobolev operators, and frozen SP-14 Target remain open.
