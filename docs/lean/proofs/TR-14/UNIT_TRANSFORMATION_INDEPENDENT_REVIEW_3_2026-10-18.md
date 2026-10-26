# TR-14 actual transformation and finite-class unit avoidance — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored none of these sources. **APPROVE these exact five new support modules.** The full contextual product lower bound and TR-14 Target remain separate obligations.

| Module | SHA-256 |
| --- | --- |
| `UnitScaleProducts` | `896d50d33f7d07325789bfc26225c4f06c85900e7fd7a39a64c9e4a8736274ce` |
| `LinearTransformation` | `3722c9a3f7f80b552391529407abbd673c3dea4c5c8614a41443f9b7890e7ebd` |
| `UnitScaleAction` | `5cb17bbe1ca52f4c36a306302e5c8fd8c2b0f7f952f068054baa77e89e07c17a` |
| `UnitTransformation` | `cf9ccb517c96ef8adba56cafd08d73bd933c985e8b63196fdada6b187237eb92` |
| `UnitAvoidance` | `f2d0fcaea7aa6a1cfab62dc335e09d44de7a0a4cc133dfe031df8019a2dc499e` |

`UnitScaleProducts` uses the explicit unit-multiplication linear equivalence, proving composition/inverse/intersection and inverse-membership identities. The transformation dimension identity is the actual subspace sum/intersection formula after this invertible scaling. Its product inclusion is exact: if x is in U and e*x is in V, and y is the sum of an element of V and e*z for z in U, then both x*y summands lie in the original product span U*V. Commutativity is an explicit ambient-ring condition. No product dimension bound is assumed.

`LinearTransformation` constructs its auxiliary subalgebra S and space T by strong induction on the actual dimension of U, generalizing V. If every unit of V is preserved by multiplication from U, the previously proved unit-span theorem extends this to every element of V, so U lies in the actual stabilizer. Choosing T=V gives stability, the inclusion in U*V and the required dimension inequality. Otherwise a concrete unit e in V and x in U violate preservation. The intersection `U ∩ e⁻¹V` strictly omits x, still contains one, and has smaller dimension. The sum `V + eU` contains one, preserves the combined dimension and has transformed product inside U*V. The induction result therefore transports to exactly `V ≤ T ≤ U*V`, `S*T ≤ T`, and the stated sum-of-dimensions bound. The recursion does not assume termination from a dimension inequality that it is trying to prove.

`UnitScaleAction` proves scaling of the actual product and retention of S-stability under a unit multiplier, using commutativity. `UnitTransformation` normalizes an actual chosen unit a in U to one, applies the constructed normalized lemma, and scales T back. Its resulting lower inclusion is exactly a*V, upper inclusion is U*V, stability uses the same S, and both dimensions are preserved. It requires only one in V and the actual chosen unit in U, in addition to the stated finite-dimensional/infinite-field ambient conditions.

`UnitAvoidance` first proves a scalar line through x outside a subspace can meet that subspace at most once: two distinct intersections would put both one and then x inside. Given finitely many subspaces proper relative to U, the finite-union theorem produces x in U outside all of them. The finite bad line parameters together with the finite spectrum of -x leave a scalar making x+c*1 simultaneously a unit and outside every forbidden subspace. This remains valid in a nonreduced ambient algebra. If finitely many sets contained in U cover its units, treating their spans as forbidden proper subspaces gives a contradiction, so one class spans U. Actual finite covering data remains an explicit hypothesis; this does not assume finitely many arbitrary ambient subalgebras or supply the later contextual finite-class application without proof.

The independent immutable-source audit passed **nine Lean commands**: these five new modules, the previously reviewed ProductStabilizer and UnitSpan, statement infrastructure, and a separate consumer. It checks **36 explicit declarations**, including **33 theorem/lemma constants**, their theorem kind, LeanCert kernel trust and transitive printed axiom closure. Only `propext`, `Classical.choice`, `Quot.sound` occur. All frozen bytes and all ten dependency pins/tracked trees pass before/after. All local objects are built in a fresh private prefix excluding campaign project objects; pinned dependency objects are reused.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/TR-14/verification/check-unit-transformation.py \
  --top UnitTransformation UnitAvoidance --evidence-name unit-transformation-review-3
```

Exact driver, sources, consumer, hashes and raw output are retained in [verification/unit-transformation-review-3/](verification/unit-transformation-review-3/). The preceding [product/context/reducedness and UnitSpan review](PRODUCT_SUPPORT_INDEPENDENT_REVIEW_3_2026-10-18.md) remains separate. These are exact algebraic support gates and local macOS Lean4.33.1 kernel evidence, not a full product lower-bound theorem, Target proof, Linux Comparator receipt, source-author endorsement or external human peer review. No proof, original target, permanent ID or canonical page was changed for this audit.
