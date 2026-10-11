# SP-14 actual base-jet real solve: independent mathematical pre-review

**Reviewer:** `/root/tr14_frob_review` (independent AI agent), 10 October 2026. **Verdict:** APPROVE the frozen real-solve contract for Lean implementation after the separate exact base-pencil polynomial receives final Lean source approval. This review does not assert a proof of `NLA.Statements.SP14.Target`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`BASE_JET_REAL_SOLVE_PRE_REVIEW.md`** | **`dce71f8dba14a042665cf27a07be3a34447db8aa3d6e80f90d85f4223fbd0a4f`** |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Audited `lean-statements/NLA/Proofs/SP14/BaseJetTriangular.lean` | `a1cff804e204a656bed6f0b45d06d0d0e0f238d385468bcda4384b72cd790ccc` |
| Base-pencil mathematical pre-review | `dd925f11d74a170dd2d1b1aba4d7f80bd69da182f3881d2b64160f36874360d6` |

## Exact checks

- The padded vector is real on the first `h` coordinates and zero on the rest. In the reviewed actual-polynomial formula, the coefficient of `X^k` for `k<h≤q` receives `-2(k+1)∑_{d=k}^{h-1}baseCoeff(d-k)u_d`; every term with `d≥h` vanishes by padding. Since `2q≤m+1`, either `m=q=h=0` or `h≤m`; hence `k<h` implies `k<m` and the base term `X^m` contributes zero. The already proved `baseCoeffReal_to_complex` turns this coefficient into the complex cast of `(baseJetMatrix h).mulVec u k`. Its imaginary part is zero, so the proposed real-part map is exactly that matrix map.
- The matrix is upper triangular with diagonal `-2(k+1)` for all `k<h`; its determinant is nonzero, including the empty determinant `1` when `h=0`. The existing audited `baseJetSolve_spec` therefore provides each desired real `y` and `baseJetSolve_unique` provides uniqueness **within the zero-padded first-`h` coordinates**. If `q>h`, the full `q`-variable first-`h` map has nontrivial kernel and must not be called unique.
- The public vector theorem must identify the coefficients of the **actual** `oddJetPolynomial (baseJetSymbol ...)`, not a model polynomial. Setting `y=0` gives first-`h` coefficient zero and therefore the existing `JetVanishing` predicate. The base solution is zero because the inverse matrix sends zero to zero; this is not an analytic all-background stage solution.
- As real functions on `Fin h→ℝ`, `F(u)=J⁰.mulVec u` implies `F(u')-F(u)=J⁰.mulVec(u'-u)` for every pair. Consequently its Fréchet derivative at every input is the same matrix-induced continuous linear map; the determinant theorem makes that derivative bijective and its row rank exactly `h`. A theorem only restating `baseJetMatrix_det_ne_zero` without connecting the derivative of `baseJetRealMap` would miss the source's regularity assertion.
- At `h=0` every coefficient, solve, uniqueness, and derivative claim is vacuous or the unique zero-dimensional map. `q=0` forces `h=0`, and `m=0` forces `q=h=0`. At `m=1,q=h=1`, `F(v)=-2v` and the solution is `-y/2`. At `m=3,q=h=2`, the map is `(-2v₀-v₁,-4v₁)`, determinant `8`, and unique supported solution `v₁=-y₁/4`, `v₀=-y₀/2+y₁/8`.

Every public coefficient, solve, and derivative theorem needs the size condition `2q≤m+1`; `baseJetRealMap` may be defined more generally, but the formula must not be generalized to arbitrary `q`. The selected-coordinate uniqueness statement may be expressed for `u : Fin h→ℝ`, or for full vectors equipped with an explicit zero-padding/support condition. The abstract `HasFDerivAt` or `fderiv` API may vary, but the derivative theorem must identify the actual real first-jet map and its matrix-induced linear map.

The all-background stage, norm budgets, infinite symbol, and final negative target remain separate. A frozen Lean source requires a new exact-signature, proof-escape, imported LeanCert kernel, and transitive-axiom review. Changed contract or source bytes reopen this review.
