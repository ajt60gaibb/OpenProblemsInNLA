# TR-14 actual whole-root supports and dimension partitions — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored neither new source. **APPROVE these exact support modules.** Final tensor blocks and the all-width Target remain separate obligations.

| Module | SHA-256 |
| --- | --- |
| `LocalBlockSupport` | `34abf64031ed15a4abf5a53459f3480d2a598272d716a5d9af0e39e3f05b2883` |
| `OrthogonalBlockDimensions` | `0b231b3e62eb86071bc5cdd16dd2f08fe4a95f180aa6853717b26792a8485264` |

`LocalBlockSupport` constructs the actual residue map at the truncated root's zero coordinate and identifies it with the actual constant coefficient. An idempotent's complex residue is zero or one. In the zero case the original element is nilpotent by the proved constant-zero property, hence the idempotent is zero. In the one case its complementary idempotent is nilpotent, hence zero, so the original is one. This uses the actual positive local multiplicity and never separates derivative coordinates within one repeated-root factor.

The true CRT equivalence therefore sends each quotient idempotent to zero or the identity on each entire truncated local root factor. Every nonzero quotient element has nonempty actual CRT support by injectivity. For pairwise orthogonal nonzero idempotents, selecting one supported root for each is injective: sharing a root would give one times one equal to zero in that factor; applying its genuine residue map gives the contradiction one=zero in ℂ. Thus the count is bounded by the number of actual distinct roots, not the total multiplicity. Completeness of the family is unnecessary for this stronger count lemma. Positive dimension of a nonzero actual multiplier range is proved by its own element e=e*1 and finite dimensionality from the monic quotient.

`OrthogonalBlockDimensions` constructs a genuine linear equivalence from B to the product of the actual multiplier ranges e_jB. Its forward map multiplies by every e_j; its inverse sums the ambient values. Completeness gives the first inverse identity; orthogonality kills every off-diagonal term and idempotence fixes the remaining actual range element for the second. No block dimensions are supplied as invariants. Finite-dimensionality then yields the exact sum of actual image dimensions equal to dim(B). Applying a genuine unital algebra homomorphism to primitive indicators preserves orthogonality and their complete sum, so the same actual dimension partition holds in the destination algebra, including the separate quotient/scalar projections. Such projected indicators can be zero and are not falsely declared primitive or nonzero. An empty family is allowed exactly when its completeness equation permits it.

Independent immutable verification passed **27 Lean commands**: 26 actual local sources plus a separate consumer, **210 explicit declarations** and **147 theorem/lemma-kind checks**. All explicit constants, including actual private imported definitions/theorems, pass declared-kind and LeanCert kernel checks with printed transitive axiom closure. Only propext, Classical.choice, Quot.sound occur. Every frozen byte and all ten dependency pins/tracked trees pass before/after. Local outputs are fresh/private, excluding campaign project objects; pinned cached dependency objects alone are reused.

```bash
python3 docs/lean/proofs/TR-14/verification/check-block-support-and-partitions.py \
  --top LocalBlockSupport OrthogonalBlockDimensions \
  --evidence-name block-support-and-partitions-review-3
```

Exact driver/source/consumer snapshots, compiler/pin identities and logs are in [verification/block-support-and-partitions-review-3/](verification/block-support-and-partitions-review-3/). Imported CRT/cyclic/reduced-classification foundations retain their separate reviews. This is independent source review and local macOS Lean4.33.1 evidence, not a completed tensor block application, full Target, Linux acceptance, source-author endorsement or external human peer review. No proof, original target, canonical page or permanent ID was changed.
