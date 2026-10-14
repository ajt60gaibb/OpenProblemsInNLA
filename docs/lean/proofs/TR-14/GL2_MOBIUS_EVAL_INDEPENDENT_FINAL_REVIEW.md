# TR-14 nonzero affine-root coordinate: independent imported review

**Disposition:** pass as a source-faithful partial gate. Root multiplicities, the point at infinity, projective support count, width equalities, and frozen Target remain open.

I reviewed `GL2MobiusEval.lean` at SHA-256 `a6ce893b0bf5d7c0fed32d3bff8224ad893fe9d94ed3a63590b06b00ea4ad737` against the source-locked mathematical [precontract](GL2_MOBIUS_EVAL_PRE_REVIEW.md) and [independent pre-review](GL2_MOBIUS_EVAL_INDEPENDENT_PRE_REVIEW.md). Its sole public theorem has exactly the proposed arguments and conclusion: for every ambient degree `d`, vector `g`, chart parameter `z`, and nonzero `t`, the actual charted dehomogenization evaluates to `t^d` times the original polynomial at `z+t⁻¹`. The proof rewrites the audited full polynomial identity termwise using `1+zt=t(z+t⁻¹)` and `d−i+i=d`; no new root or multiplicity assertion is introduced.

Pinned Lean 4.33.1 direct compilation and a module build of 3,037 jobs passed. A separate importing file checked the exact signature with an example, `#assert_trust kernel`, and `#print axioms` under `set_option leancert.trust "kernel"`. It reported only `[propext, Classical.choice, Quot.sound]`. The source contains no `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide`. Aggregate import remains the next gate.
