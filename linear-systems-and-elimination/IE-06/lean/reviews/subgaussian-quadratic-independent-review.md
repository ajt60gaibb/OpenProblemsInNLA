# Independent exact-code review: subGaussian quadratic concentration

Source SHA-256: `ba9231681db8d4e80e5cab9752b5cffe40c5af4fd28fdf2c368f89d256d7f4c6`. Reviewer: independent mathematical-review agent. Verdict: approved. This follows the prior hash-bound contract approval and the separately approved equivalent auxiliary-Gaussian normalization.

The scalar proof uses the actual N(0,2) density and the exact identity φ₂(z) exp(z²/8)=√2 φ₄(z). For a scalar proxy-one subGaussian Y, the joint integrand is exp((z/2)Y); its Y-integral is dominated by exp(z²/8). The implementation proves outer-integrability by domination, section-integrability from HasSubgaussianMGF, and joint integrability before swapping the integrals. The Gaussian MGF then gives exp(Y²/4) and the stated integral bound √2.

DirectionalSubGaussian is explicitly the full collection of linear-projection MGF bounds with proxy ∑vᵢ². Each actual matrix column is normalized by its Euclidean norm; total division at a zero column is harmless and explicitly supported by the zero-column lemma. The normalized proxy is at most one. Nonnegative weights columnSq/F² sum to one, and pointwise finite Jensen yields the Frobenius quadratic moment without any independence between columns or projections. Integrability follows by domination by the finite sum of the scalar moments.

The ENNReal strict-event tail uses the exact threshold (2+4x)F². Its Markov integrand scales by exp(−1/2−x); √2≤exp(1/2) is proved symbolically from the exponential lower bound, giving exp(−x). If F²=0 then every entry and the quadratic vanish, so the event is empty. The public x≥0 and probability-space hypotheses are exactly the reviewed contract. Empty dimensions are covered.

This is a conditional auxiliary theorem with an explicit directional MGF assumption. It does not prove that a restricted Gaussian law has that property, nor does it prove IE-06’s final growth estimate. The source has no custom axiom, native evaluation or unproved premise concealed as an implementation theorem. The author reports all 19 declaration checks passing with foundational axioms only; root whole-package verification remains separate evidence.
