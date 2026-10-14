# SP-14 base jet matrix: independent partial Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `BaseJetTriangular.lean` for the source's explicit real triangular matrix and its unique real linear solve. This is a proper subset of the [approved constructive base-jet contract](BASE_JET_RIGHT_INVERSE_INDEPENDENT_PRE_REVIEW.md); it does **not** identify that matrix with the actual frozen Toeplitz jet Jacobian.

I read the complete source and compared its definitions with the canonical source's `J⁰`. The entry at row `k`, column `d` is `−2(k+1) choose(1/2,d−k)` when `k≤d`, and zero otherwise. The real half-binomial coefficient is proved to cast exactly to the reviewed complex `baseCoeff`. The matrix is upper triangular, including the empty `h=0` case, with diagonal `−2(k+1)`; its determinant is the product of these nonzero real factors. `baseJetSolve h y` is the inverse-matrix product for **every** real target vector, and the source proves it is the unique solution of `J⁰x=y`.

These are exact finite linear-algebra claims with no floating-point computation. They do not prove that any corrected symbol has a particular jet, that `J⁰` equals the derivative of the actual finite Toeplitz jet map, or that the perturbed-background stage has a right inverse. The all-`m,q` actual-polynomial identity, Fourier bridge, and final `SP14.Target` remain open.

I independently ran a separate **imported** LeanCert audit under pinned Lean 4.33.1. It elaborated the three public definitions and eight theorem signatures, ran `#assert_trust kernel` on every theorem, and printed transitive axioms for the key cast, determinant, and solve theorems. The audit exited 0; those theorem closures use only `[propext, Classical.choice, Quot.sound]`. The frozen source contains no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseJetTriangular.lean`** | **`a1cff804e204a656bed6f0b45d06d0d0e0f238d385468bcda4384b72cd790ccc`** |
| Approved `BASE_JET_RIGHT_INVERSE_PRE_REVIEW.md` | `bbcb1bfe929f05bfdfe1a34e5e34b8d021b2aff365c8c60e7ec4900a16f1ee4d` |
| Independent mathematical pre-review | `a113d2aa973448e6ee07ca20e69833b34f84353b68900b68655908263946fd4a` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Imported `/private/tmp/sp14-basejettriangular-independent-audit.lean` | `c78a54f790f3d4c6f54cb76e9f7652fbdcd919dfc69926950125732dd2c6fe4e` |

Changed source or contract bytes reopen this review.
