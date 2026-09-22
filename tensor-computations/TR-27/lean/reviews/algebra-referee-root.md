# TR-27 Algebra independent module review

Reviewer: `/root`, Codex AI agent, 2026-09-22. Author: `/root/canonical_inventory`. I did not implement this module. I authored separate semantic modules, so this is an independent **Algebra-module** review, not an independent review of a future complete TR-27 package or human peer review.

Verdict: **APPROVE** the three frozen signatures `integral_quadratic`, `quotient_semantics`, and `curve_nonzero`, and their 16 displayed supporting declarations. This approves no complete counterexample or publication status.

I read the complete source and checked its definitions against the frozen Challenge. The quadratic uses coordinate 1 for exponent label 2; expansion cancels exactly. The quotient is a genuine linear map over complex numbers. Its surjective preimage sets source coordinate 1 to zero and divides all retained coordinates by the nonzero constant 5. The kernel proof reconstructs every source coordinate as `(-w 1 / 5) • center`, including the omitted coordinate, and proves the reverse inclusion through the linear map. The finite coordinate case splits are exhaustive fixed-dimension algebra, not sampling parameter values.

For finite curve parameters, vanishing of coordinate zero forces `t=5/3`, and coordinate one then contradicts that value; infinity has nonzero final coordinate. Thus all complex parameters and infinity are covered. The target's first coordinate is exactly -3. The three-term identity follows from the exact center kernel identity and linearity. The homogeneous charts coincide with the finite and infinity curve representatives. The border polynomial has first coordinate -3 for every parameter, equals the target at zero, and agrees with the divided difference for every nonzero complex parameter. The latter proof divides only after the explicit nonzero hypothesis. No rank, closed-image, admissibility, or border-closure fact is assumed or claimed by these helpers.

I independently rebuilt Definitions and Algebra in fresh external directory `/private/tmp/nla-tr27-root-algebra-review`, then ran the retained 19-declaration axiom audit against that build. Both exited zero with no warnings; every closure is exactly `propext`, `Classical.choice`, `Quot.sound`. Source has no Challenge import, placeholder, native computation or custom axiom. These are cached local development checks, not Linux Comparator or complete dependency source reconstruction. Attribution distinguishes Colbrook's mathematical counterexample from George Stepaniants's formalization and requested Caltech affiliation; no contact email is added.

The broad Mathlib tactic import could later be narrowed to reduce build dependencies, but does not weaken trust or alter the exact target. Any mathematical source changes require renewed review.

## Reviewed byte binding

- `NLA/TR27/Algebra.lean`: `ce5694407e1e40b201746dc52897ea05acbb69c27efa6c79bfb700fe070d5134`
- `NLA/TR27/Definitions.lean`: `5f9cbf71a854a8a8a968ea4713c12bf501726e294ed7cccacff390dafb687056`
- `Challenge.lean`: `158b0f5d8eb23a3165caecf7ceed5c3f6ab87310c0576bbe9f57cbe3cfbe0ee5`
- `reviews/root-algebra-typecheck.log`: `367dc2b671ffcadf75661ce506dc5601ccb348ecaaf64b2d4ce3d097ba0c43a7`
- `reviews/root-algebra-axioms.log`: `9efaf0e3a1320ab54dd404711bbd9ad03145f5cf8903d67178559b734ce4c98c`
