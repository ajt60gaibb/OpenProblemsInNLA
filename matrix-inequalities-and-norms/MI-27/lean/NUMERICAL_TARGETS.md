# Exact numerical obligations before proof implementation

This is an unelaborated source-stage specification. No numerical certificate, Lean run or Comparator run has occurred in this directory. Root plus a fresh nonauthor reviewer must approve the actual elaborated source statements and their immutable freeze before proof bodies.

**N01 / C01:** prove exactly `(0 : ℝ) < 1 / 2` with the pinned LeanCert default-kernel path. The input is the singleton rational constant 1/2. No subdivision, parameter search or matrix-size grid is justified. Its actual proof-body consumer must be C05: use positivity when simplifying the scalar norm and multiplying the operator-norm estimate in `[Q,H] = (1/2)[2Q-I,H]`. A disconnected unused numerical theorem is insufficient. Keep the closed kernel certificate and the final dependency path. No native-decide trust shortcut or new axiom is permitted.

**N02 / C13–C14:** for every a,b > 0 with a+b = 1 and every R ≥ 1, prove interval integrability, the exact primitives and bounds for

`kernelAB a b γ = a*b / (γ*(b+a*γ))`,
`kernelBA a b γ = a*b / (γ*(a+b*γ))`.

Their integrals on [1,R] are `a*log(R/(b+a*R))` and `b*log(R/(a+b*R))`. They are nonnegative and bounded respectively by `-a*log a` and `-b*log b`; their sum is at most h a b. This is symbolic scalar calculus and logarithm monotonicity, including R = 1. No improper quadrature, numerical tails or transcendental enclosures are proposed.

**N03 / C10:** derive a common positive spectral lower bound ε for each strict density pair and the upper bounds ρ,σ ≤ I. Then R = 1+ε⁻¹ is greater than one and simultaneously annihilates both hockey-stick terms for every unitary conjugate and every γ ≥ R. The bound is existential and input-dependent, not a final conditioning premise or a numerical eigenvalue approximation.

C11 and C16 contain noncommutative mathematics that these numerical obligations do not prove. C12 additionally requires distinct mixture cutoffs R/(b+aR) and a+bR before their substitutions. All these obligations remain symbolic and internal; only the full C20 theorem can increment the completed original-target verification count.
