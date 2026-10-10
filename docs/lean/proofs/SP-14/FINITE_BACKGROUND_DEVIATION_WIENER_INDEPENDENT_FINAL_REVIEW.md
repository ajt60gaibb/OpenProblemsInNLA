# SP-14 finite-background deviation Wiener bound: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen actual-curve bound for aggregate import. It is the full reviewed finite-background W^(9/8) deviation estimate, not the complete SP-14 counterexample or frozen negative Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/FiniteBackgroundDeviationWiener.lean` | `17a23185670dd279a969969102ea19c8f3242ac72f4514e8345fe6f632efb22e` |
| Exact canonical first-smallness contract | `c763ef118c85bbf178fea605a0ef9693932d287ed6308207c53b883ce4f9a596` |
| Separate imported audit `/private/tmp/sp14-finite-background-deviation-independent-audit.lean` | `5e0a708c8f2fe0587168742a947f81980940a072866b37519e800e9e69033cf5` |

The first theorem takes actual same-length finite endpoint quotients `P₋=(1+s)Q₋`, `P₊=(1+s)Q₊`. It rewrites the already audited actual curve exactly as `h−s=2s F(Q₋+Q₊)+sP²`, where `F=regularizedBaseFactor=(1+s)g₀` and `P=P₋+P₊`. Audited positive/negative finite multiplier estimates, addition, square, and circle-mode shift give literal weighted Fourier summability and

`W^(9/8)(h−s) ≤ 2·2^(9/8)·W^(9/8)(F)·(W^(9/8)(Q₋)+W^(9/8)(Q₊)) + 2^(9/8)·(W^(9/8)(P₋)+W^(9/8)(P₊))²`.

The second theorem derives both finite quotients from the **separate** contact premises `P₋(-1)=0` and `P₊(-1)=0` and returns their factorization along with the same bound. It retains all finite `u,v`, including zero, and the actual `finiteBackgroundCurve` on the left. The `2` and `2^(9/8)` coefficients are exactly those in the independently reviewed contract; no surrogate coefficient norm appears.

The direct pinned Lean 4.33.1 module build passed 2,777 jobs. A separate imported audit checked both public signatures, reran LeanCert kernel trust, and printed only `[propext, Classical.choice, Quot.sound]`. A source scan found no proof escape. Changed source bytes require a new review. The strict two-mode threshold witness, stagewise packet control, inverse bounds, and full negative Target remain open.
