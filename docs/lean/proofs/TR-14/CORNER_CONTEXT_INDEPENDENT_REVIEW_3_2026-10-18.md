# TR-14 exact contextual data in intrinsic corners — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored no TR-14 source. **APPROVE `CornerContext.lean` at SHA-256 `f1de8589c8e0f13baaaaac6fd2df3233c257bcbb00181879b081aec327632ad1`.** It transports actual contextual data; the final block/lower-bound application remains separate.

The defining quotient relation gives projection(e)=1. For an actual idempotent, projection composed with the ambient inclusion is identity, while inclusion values are fixed by multiplication by e. The product-corner projection is a genuine unital algebra map to the two factor quotients, and the product-corner inclusion is injective, linear and multiplicative with identity mapping to e. These are correctly separate maps, including zero factor corners.

The intrinsic block space is the actual image of U under that quotient projection, and its actual ambient inclusion image is exactly U multiplied by e. The block functional is the original functional composed with the actual inclusion, so it evaluates a projected x as Λ(e*x). A one-containing space maps to a space containing the intrinsic block identity. Genuine unital algebra images commute with actual list submodule products, including an empty scalar-one product; this is proved by list induction, not assumed as a product-space oracle.

If e belongs to the actual stabilizer of W, then e*x remains in W for x in W, so the original annihilation gives annihilation of the actual corner image. Frobenius nondegeneracy on A restricts to its genuine corner: test an intrinsic a against the quotient images of all ambient b, use that its inclusion is fixed by e to remove the extra e factor, then apply the original Frobenius condition and injectivity. No nonzero first corner is needed. Full first projection of a real ambient subspace remains full first projection of its actual corner image by choosing a quotient representative and then the provided ambient lift.

Thus every listed inheritance statement concerns the same original spaces and functional via the actual quotient/inclusion. None assumes a corner is just a renamed ambient ideal, falsely treats ambient inclusion as unital, or supplies an independent Frobenius/projection predicate. A final tensor application must still supply the genuine stabilization, annihilation and complement projections.

Independent immutable verification passed **18 Lean commands**, 17 actual local sources plus a consumer, **93 explicit declarations** and **79 theorem/lemma-kind checks**. All constants pass LeanCert kernel trust and printed transitive axiom checks with only propext, Classical.choice, Quot.sound. Source bytes and all ten dependency pins/tracked trees pass before/after. Local outputs are fresh/private, excluding campaign project objects; pinned cached dependency objects alone are reused.

```bash
python3 docs/lean/proofs/TR-14/verification/check-corner-context.py \
  --top CornerContext --evidence-name corner-context-review-3
```

Exact sources, consumer, driver/compiler hashes, pins and logs are in [verification/corner-context-review-3/](verification/corner-context-review-3/). The two basic corner modules and earlier contextual iteration retain their separate reviews. This is independent source review and local macOS Lean4.33.1 evidence, not full Target proof, Linux Comparator acceptance, external human peer review or source-author endorsement. No proof, original statement, canonical page or permanent ID was changed.
