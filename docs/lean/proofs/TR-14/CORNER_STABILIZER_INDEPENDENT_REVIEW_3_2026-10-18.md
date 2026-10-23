# TR-14 actual primitive-corner stabilizer — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored no TR-14 source. **APPROVE `CornerStabilizer.lean` at SHA-256 `8c0fbebebf4a0731a3bea9b0c19128cb6c401f3ffead3f63a27bb5d1caef5ccd`.** This proves the needed scalar-stabilizer consequence from an actual primitive algebra decomposition; the full tensor block application remains separate.

An intrinsic corner stabilizer element z extends by the actual ambient block inclusion. For any w in W, projection(w) belongs to the actual block image, so z*projection(w) is the projection of some actual a in W. Its ambient inclusion is e*a, which lies in W because the same idempotent belongs to the actual global stabilizer. Multiplicativity and the inclusion's fixed-by-e property identify this value with inclusion(z)*w. Thus the zero-extended multiplier genuinely belongs to the global stabilizer. No direct-sum or complement-invariance oracle is required.

For a primitive indicator obtained from the actual complex algebra equivalence `φ : productStabilizer W ≃ₐ[ℂ] (Fin t → ℂ)`, the ambient inclusion a of z is in that global algebra and satisfies a*e=a. The previously proved actual primitive scalar-action formula gives a*e=φ(a)_j*e. Injectivity of the actual corner inclusion then yields z=φ(a)_j*1 in the intrinsic product corner. The theorem therefore derives the scalar action rather than taking a trivial-stabilizer assumption. Its actual algebra equivalence remains explicit and must be supplied by the proved reduced-algebra classification in the tensor application.

Finally the intrinsic stabilizer's underlying subspace lies in the span of its own identity, giving actual finite rank≤1 by subspace monotonicity and singleton-span dimension. No additional nontriviality or proper-quotient assumption is used; zero factor corners retain their exact meanings. Ambient finite dimensionality is required only for the dimension bound and is inherited by the genuine quotient factors.

Independent immutable verification passed **20 Lean commands**: 19 actual local sources plus a separate consumer, **105 explicit declarations** and **90 theorem/lemma-kind checks**. All constants pass LeanCert kernel trust and printed transitive axiom checks; only propext, Classical.choice, Quot.sound occur. Source bytes and all ten dependency pins/tracked trees pass before/after. Local outputs are freshly rebuilt in a private prefix excluding campaign project objects; pinned dependency objects alone are reused.

```bash
python3 docs/lean/proofs/TR-14/verification/check-corner-stabilizer.py \
  --top CornerStabilizer --evidence-name corner-stabilizer-review-3
```

Exact frozen sources, consumer/driver, hashes and raw output are in [verification/corner-stabilizer-review-3/](verification/corner-stabilizer-review-3/). Earlier corner/contextual/reduced-classification semantics retain their separate source reviews. No proof, statement, original page or permanent ID was edited. This is independent source review and local macOS Lean4.33.1 kernel evidence, not full Target proof, Linux Comparator acceptance, external human peer review or source-author endorsement.
