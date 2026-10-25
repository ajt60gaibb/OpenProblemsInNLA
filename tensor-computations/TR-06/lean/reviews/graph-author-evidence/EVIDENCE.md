# TR-06 graph-Jacobian linear inequalities

Author: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Original TR-06 mathematical proof remains attributed to Matthew J. Colbrook. No contact email was added, and frozen Definitions/Challenge/canonical source were untouched.

Final source: `NLA/TR06/GraphJacobian.lean`, SHA-256 `c1d34a779cbd1d99987cdcf28090298c7e2745745a32be12b2787f1d02f6173c`.

## Statement review

Root independently approved the exact definitions and signatures before implementation. `STATEMENT-PLAN.md` records the mathematical route; `PRE-PROOF-APPROVAL.md` records the approval. The actual approved draft is retained at `evidence/approved-draft.lean`, with matching SHA-256 `78c9b8dd1fbdcf6368563de240ed3d45641f0a66217d4d02dcf8bebe225ced3b`. All three map definitions and both approved theorem statements remain unchanged.

The first theorem, `opNorm_le_normDet_graphL2Map`, proves `‖T‖ ≤ normDet (x ↦ (x,T x))` for finite-dimensional real inner-product spaces E and F. The codomain is explicitly `WithLp 2 (E × F)`, not the ordinary max-norm product.

The second, `opNorm_rangeInverseOperator_mul_normDet_le`, proves `‖B ∘ A_range_inverse‖ * normDet A ≤ normDet (x ↦ (A x,B x))` for the actual inverse of injective A onto its induced-norm range, with the paired map into `WithLp 2 (F × G)`. All spaces retain the reviewed finite-dimensional hypotheses. Both statements include domain dimension zero, with no extra positivity assumption.

## Proof

For the first statement an orthonormal eigenbasis for `T* T` gives nonnegative eigenvalues ev_i. The graph Gram matrix is proved entrywise to be diagonal with entries `1+ev_i`, so its norm determinant squared is their product. Since each factor is at least one, the product bounds every ev_i. An exact orthonormal quadratic expansion of `‖T x‖²`, using the adjoint and symmetry, bounds it by `normDet graph² * ‖x‖²`. Nonnegative square comparison and the operator-norm bound theorem yield the result. The argument uses the same finite sums and products when the basis is empty.

For the second statement the paired map is explicitly factored as A restricted to its range, the graph of the actual range-inverse operator, and the L2 product of the range inclusion isometry with the identity on G. The final isometry preserves norm determinants. The first factor has equal-dimensional domain and range, so norm determinants multiply exactly; codomain restriction preserves A's norm determinant. Multiplying the first graph inequality by A's nonnegative norm determinant gives the approved inequality.

The second proof actually needs only the finite-dimensional range of A, but its reviewed ambient F finite-dimensional interface is retained. A local style-linter option suppresses only the unused-section-variable warning for that intentionally retained hypothesis; it changes no proof trust or axiom checking.

## Verification and limits

The final pinned Lean 4.33.1 run exited 0, with no warnings or errors. Both exported theorem closures use only `propext`, `Classical.choice`, and `Quot.sound`; both LeanCert `#assert_trust kernel` checks passed. Their closures include the private graph-Gram identity and isometry composition helper. No Challenge import, sorry/admit, extra axiom, native computation oracle, numeric certificate, or desired conclusion assumed as a hypothesis is used.

The final command, environment search paths, timestamp, source/Definitions/plan/approval hashes and exit code are retained in `evidence/receipt.json`; actual compiler/axiom/trust output is `evidence/GraphJacobian.log`. `check.py` reproduces the local compilation. These are supporting inequalities, not nonlinear area formulas, graph-volume finiteness, generic regularity, nullity, radial integration, or finite-expectation results. This is not a completed TR-06 Comparator verification.

Original sources: [canonical TR-06](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/tensor-computations/TR-06/README.md), [Matthew J. Colbrook manuscript](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/references/colbrook-unclaimed-2026-09-11/manuscripts/TR-06.md).
