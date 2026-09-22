# IE22 exact Gaussian variance author report

AI proof author: `/root/infrastructure_audit`, also author of some vendored IE21 Gaussian modules. This is an author report, not an independent final review. `VarianceTensorization.lean` was authored separately by `/root/ie21_final_correctness`.

The exact frozen selected `gaussian_objective_variance` now has a complete proof. For arbitrary real θ, natural m,d≥1, any real matrix B and every t≥0, it proves MemLp of the literal `projectedObjective` at exponent two under the actual `stdGaussian (Space d)`, together with Var ≤ 4*t*operatorNorm B²/m. It retains the original floor-based trimming dual. It imposes no row norm or row independence hypothesis. The dimension hypothesis is included in the theorem signature, although the proof also works in dimension zero.

The three owned modules are frozen at these SHA256 values:

- `GaussianPoincare.lean`: a0636eda1a4493fe981908fe061efc4e4f65cb4772e2d01a248962d0f0b4010c
- `GaussianPoincareHinge.lean`: 948b4515ceb96429dcc6ed8b3c3c004d3924eb6952e2ca9f0a5d7ea64f8ef941
- `GaussianVariance.lean`: 11682dad1bcb30d3fbea714ca1d2dd0ffe1b3f67a294a4b423dd15bcfbb4905c

The scalar foundation derives the exact-one Gaussian inequality by the independent-copy variance identity, truncated Gaussian first moments and a nonnegative Tonelli crossing-kernel calculation. The hinge module discharges all of that foundation's premises: finite affine hinge sums are absolutely continuous, possess the explicit derivative almost everywhere, and have bounded measurable objective and derivative. Zero coefficients, threshold equalities, t=0 and zero-length intervals are treated explicitly. The interval-energy estimate follows from absolutely continuous FTC and integrating a nonnegative square.

The matrix module identifies each coordinate fiber with that literal affine hinge sum. It uses the actual derivative vector (2/m) B* applied to the active row values. The sum of squared active row values is at most m*t, and the adjoint operator norm equals ‖B‖, giving the exact factor four. Finite-product tensorization and coordinate resampling then sum the scalar bounds. The final transport is Mathlib's actual `map_pi_eq_stdGaussian`; no proxy distribution is substituted. Every integral comparison uses proven integrability.

`final-build.py` created a new external build directory and compiled Definitions, the independently authored Tensorization, all three owned modules and an exact selected-signature test. All six commands exited zero without warnings or errors. `FinalAxioms.lean` printed all 52 owned public theorem closures, each a subset of propext, Classical.choice and Quot.sound. The receipt records the actual source and binary hashes, commands, log, 31 unchanged vendored IE21 source hashes and reused IE21 olean hashes. It verifies source bytes are unchanged after the build. Earlier failed development iterations are retained.

This is a local author verification using cached third-party dependencies and unchanged previously verified IE21 modules. It is not an authentic full Linux LeanCert/Comparator result. Independent module and final whole-package reviews, immutable publication inputs, permitted-axiom checks and the complete shared Linux verifier remain required before IE22 completion or status promotion.
