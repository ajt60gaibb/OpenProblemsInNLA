# TR-14 actual primitive indicators and block polynomial dimensions — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored none of these sources. **APPROVE these exact three algebraic support modules.** They do not construct the final tensor blocks or prove full Target.

| Module | SHA-256 |
| --- | --- |
| `ReducedPrimitiveBlocks` | `d80c1acdfe8916ffcfdc7700bd441b701eb596fff4023502af7e42b9b23c96cd` |
| `CyclicSpanDimension` | `c430e82a28d5c738da7aa969c193008e7a7a223270d9845470809cfb1415f009` |
| `BlockPolynomialImage` | `13ad26f8cbdc29ed19f398335c9db90a7783a6f9019363e39413c7405b463b6a` |

`ReducedPrimitiveBlocks` constructs an actual complex algebra equivalence from a reduced finite-dimensional commutative complex algebra to a finite product of complex copies. The Artinian residue-field decomposition is used with actual residue extensions, proved finite/integral over ℂ and hence scalar by algebraic closedness. Pulling coordinate indicators back through that actual equivalence gives ambient idempotents of the subalgebra: membership, nonzeroness, pairwise orthogonality, sum equal to ambient one, and multiplication by each subalgebra element equal to its actual scalar coordinate. These indicators are primitive relative to that reduced subalgebra; no ambient reducedness or ambient primitive classification is asserted. A zero algebra and an empty product are not excluded.

`CyclicSpanDimension` defines the actual first-n orbit span and the actual full orbit span for any linear endomorphism and vector over a field. The successor prefix adds exactly the next vector. If that next vector already lies in the prefix, applying the endomorphism preserves every prefix generator, hence the whole prefix; it also contains the initial vector, so it contains the entire orbit. Otherwise dimension strictly increases by one. Induction gives the exact prefix dimension min(n,dimension of the full orbit), including n=0, a zero initial vector and already-saturated prefixes. No cyclic-rank, minimal-polynomial or independence oracle is supplied.

`BlockPolynomialImage` identifies the full cyclic orbit of e under quotient-root multiplication with the actual multiplication range eA, using the monic quotient power basis in both directions. Its finite prefix is exactly the span of e, e*root, and subsequent available powers. The actual finite coefficient linear map has that exact span as its range, by coordinate-basis witnesses. Applying the preceding proven cyclic dimension formula gives min(n,actual dimension of eA), both for the span and the actual coordinate map. The multiplier e is arbitrary here: idempotence, nonzeroness, a supplied block rank and a positive prefix length are unnecessary. This correctly covers zero multipliers, n=0 and the degree-zero monic/unit quotient. The eventual primitive-idempotent application is an instantiation of this stronger actual-image theorem.

Independent immutable verification passed **ten Lean commands**: nine actual local sources and a separate consumer. It audits **48 explicit declarations**, including **38 theorem/lemma-kind checks**, kernel trust and transitive printed axiom closure. Private imported foundation constants are resolved by actual names and checked with their declared kind. Only propext, Classical.choice, Quot.sound occur. All source bytes and all ten dependency pins/tracked trees pass before/after; local outputs are freshly rebuilt in a private prefix excluding campaign project objects, with pinned dependency objects reused.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/TR-14/verification/check-primitive-block-dimensions.py \
  --top ReducedPrimitiveBlocks BlockPolynomialImage \
  --evidence-name primitive-block-dimensions-review-3
```

Exact frozen sources, consumer/driver, hashes and raw logs are in [verification/primitive-block-dimensions-review-3/](verification/primitive-block-dimensions-review-3/). Imported quotient/reduced-subalgebra semantics retain their earlier reviews. No proof, statement, permanent ID or original page was edited. This is independent source review and local macOS Lean4.33.1 kernel evidence, not the eventual block lower bound, full Target, Linux acceptance, source-author endorsement or external human peer review.
