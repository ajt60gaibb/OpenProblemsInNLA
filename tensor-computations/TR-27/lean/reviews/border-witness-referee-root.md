# TR-27 BorderWitness independent module review

Reviewer: `/root`, Codex AI agent, 2026-09-22. Author: `/root/reference_review`. I authored none of BorderWitness or its concrete Algebra/IntegralImage/Geometry dependencies. I authored separate projective semantic modules, so this is an independent module review, not independent final review of the whole package.

Verdict: **APPROVE** exact frozen `border_curve_semantics` and `border_two`, with seven supporting declarations. No complete rank counterexample or canonical verification is approved here.

The two-term expression uses the full cone points g(t) and g(0), with exact coefficients t⁻¹ and −t⁻¹ under the explicit t≠0 hypothesis. Nonzero curve values and the extension at zero come from the independently reviewed algebraic identities; no limiting denominator is evaluated at zero. The polynomial coordinate definition has constant first coordinate −3 and all other displayed exponents match the frozen borderCurve.

Substitution is an actual algebra homomorphism into univariate complex polynomials and evaluation is proved to commute for every complex parameter, including zero. To prove a polynomial that vanishes away from zero is identically zero, the proof multiplies it by X, evaluates at all parameters, applies polynomial extensionality over the infinite complex field, then cancels the nonzero polynomial X in the integral domain. Thus every polynomial vanishing on the entire rank-at-most-two cone vanishes along the whole extension and at the witness value t=0. The final theorem quantifies the actual complete vanishing ideal in affineClosure; it neither substitutes Euclidean closure nor checks only selected equations.

I rebuilt Definitions, Algebra, IntegralImage, Geometry and BorderWitness in a fresh external directory, then independently ran the nine-declaration axiom audit against those outputs. All exited zero without warnings, and every closure is exactly `propext`, `Classical.choice`, `Quot.sound`. There is no Challenge import, placeholder, native computation, custom axiom or finite sampling. These are cached local checks, not the full Linux Comparator gate. Original Colbrook mathematical credit, George Stepaniants formalization credit and the requested Caltech affiliation are preserved without contact email.

## Reviewed byte binding

- `NLA/TR27/BorderWitness.lean`: `2f19534138b25ca09056ef1a106565d7ad2d39394bca6b6fa75f33901f49b068`
- `NLA/TR27/Geometry.lean`: `4f067416b429e37e0b34a24d764cc75d895ca7b6bcbfb20c42edd8f5c2809472`
- `NLA/TR27/Definitions.lean`: `5f9cbf71a854a8a8a968ea4713c12bf501726e294ed7cccacff390dafb687056`
- `Challenge.lean`: `158b0f5d8eb23a3165caecf7ceed5c3f6ab87310c0576bbe9f57cbe3cfbe0ee5`
- `reviews/root-border-witness-typecheck.log`: `50d363b257a1357ec1afae9dabe8f145a565e41154880cd57a0c6036a831c7cd`
- `reviews/root-border-witness-axioms.log`: `2f0cb8d0513ebabeb2524de002b65090b15529fccf073fcd2d1fdf26499efed9`
