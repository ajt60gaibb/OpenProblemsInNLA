# TR-27 IntegralImage independent module review

Reviewer: `/root`, Codex AI agent, 2026-09-22. Author: `/root/reference_review`. I did not implement this module. I authored separate semantic modules, so this is independent review of IntegralImage only, not independent final review of the complete package or human peer review.

Verdict: **APPROVE** the exact frozen `substitution_integral` and `whole_closed_image` statements and ten supporting exported declarations. No complete rank counterexample or canonical verification is approved.

I read the complete implementation and checked the mathematical route against the frozen definitions. The local algebra structure is induced by the actual coordinate-substitution homomorphism. Its constant and coordinate integral elements are images of actual ring elements, not new integral assumptions. The polynomial for the first parameter's twelfth power is monic with coefficients `(8H0+9H2)/85` and `-5H0²/85`; exact expansion verifies the equation. Recovering the mixed monomial divides only by constant 3, and recovering the second twelfth power divides only by constant 5. Positive-power integrality then proves each parameter integral, and structural polynomial induction proves integrality of the entire homomorphism. No pointwise argument is silently used as a ring identity: polynomial extensionality over the infinite complex field supplies that bridge.

For the difficult reverse image inclusion, an arbitrary point of the full zero locus gives its actual maximal evaluation ideal M. Vanishing of every kernel polynomial proves `ker(algebraMap) ≤ M`, exactly the hypothesis required when the integral map need not be injective. Lying over supplies a maximal ideal N with contraction M; the complex Nullstellensatz identifies N with evaluation at an actual parameter pair u. Applying the contraction to each coordinate difference `Xj - wj` proves H(u)=w. The forward inclusion evaluates every kernel equation after substitution. Thus the proof covers the entire zero locus and does not restrict to a chart or selected parameter subset.

The exhaustive parameter-cone equality splits on the first parameter being zero, uses the infinity chart for that case and the finite ratio for the other, and treats the zero vector explicitly. Conversely, algebraic closedness supplies a twelfth root for every scalar and homogeneity transports both charts. Every scalar, every finite parameter and infinity is included. Fixed finite-coordinate ring expansions establish homogeneity, with no numerical sampling, transcendental approximation or native trust.

I independently rebuilt Definitions, Algebra and IntegralImage in fresh external directory `/private/tmp/nla-tr27-root-integral-review`, then reran the 12-export axiom audit. All elaborations exited zero without warnings and every closure is exactly `propext`, `Classical.choice`, `Quot.sound`. No Challenge import, placeholder or custom axiom appears. These are cached local development checks; real Linux Comparator, independent complete-proof review, geometry and rank results remain separate obligations. Original Colbrook credit and the requested formalization name/affiliation are preserved without contact email.

## Reviewed byte binding

- `NLA/TR27/IntegralImage.lean`: `72e1d5af05acc5e7497d1db2f81d6c3585497a76bdcc4577eea6c2efa783bd89`
- `NLA/TR27/Algebra.lean`: `ce5694407e1e40b201746dc52897ea05acbb69c27efa6c79bfb700fe070d5134`
- `NLA/TR27/Definitions.lean`: `5f9cbf71a854a8a8a968ea4713c12bf501726e294ed7cccacff390dafb687056`
- `Challenge.lean`: `158b0f5d8eb23a3165caecf7ceed5c3f6ab87310c0576bbe9f57cbe3cfbe0ee5`
- `reviews/root-integral-image-typecheck.log`: `6822b8e6547c8564f3403058eb673a4aa2c7e2bc3933047a404a60e1d9da5f08`
- `reviews/root-integral-image-axioms.log`: `45da93cebab8108c3311ac05367533a6f3608696a9ff8c85c2bd5340d6de9ced`
