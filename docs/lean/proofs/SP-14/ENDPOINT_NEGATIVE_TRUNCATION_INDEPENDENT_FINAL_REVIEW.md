# SP-14 weighted-sequence truncation density: independent final review

**Source author:** `/root/sp14_base_proof`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this exact infinite-extension precursor for aggregate import.

The source-locked `ENDPOINT_INFINITE_NEGATIVE_OPERATOR_PRE_REVIEW.md` at the time of implementation was SHA-256 `d9812ed8dbbee37467b342d4419d9c6688add126da9cb3b9485f2e51fee4ce75`. Its row-summability proof plan was later corrected and re-reviewed separately; the truncation-density assertion here is unchanged. The frozen source `lean-statements/NLA/Proofs/SP14/EndpointNegativeTruncation.lean` is SHA-256 `7454b7819bae6d5292bcaf53b482371adda48b7f8d55640395e542d08db47c06`.

I checked that the theorem is exactly `sobolevTruncation s N y → y` in the literal `SobolevCoeff s = lp ℂ 2` carrier, for every real `s` and every `y`. The source identifies the actual first-`N` truncation with the finite sum of `lp.single` coordinates and applies pinned `lp.hasSum_single`; it includes `N=0` and no auxiliary compact-support hypothesis.

The direct pinned Lean 4.33.1 module build passed. My separate imported exact-signature audit `/private/tmp/sp14-endpoint-negative-truncation-independent-audit.lean` is SHA-256 `b3c3535215f8c2af7a2d82f5a2dd8c03145298a4cbe78be49f0ac551fa4d031f`; LeanCert `#assert_trust kernel` passed and the transitive axioms were exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no proof escape. Changed source bytes require a new review.

No row summability, infinite negative operator, two-sided extension, or frozen SP-14 `Target` is proved by this density gate.
