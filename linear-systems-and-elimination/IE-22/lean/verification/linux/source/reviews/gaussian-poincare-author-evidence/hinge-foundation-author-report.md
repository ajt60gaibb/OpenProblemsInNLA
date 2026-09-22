# IE22 actual affine hinge regularity

AI proof author: `/root/infrastructure_audit`; not an independent final reviewer.

The stable source `GaussianPoincareHinge.lean` proves `affineHingeSum_gaussian_variance` for arbitrary finite size m, constants c,q, coefficients a,b and threshold t≥0. It applies the previously proved exact-one scalar Gaussian inequality only after discharging every premise. Each max(t−(a*s+b)^2,0) is locally Lipschitz and therefore absolutely continuous on compact intervals. Its explicit derivative exists away from two points when a≠0; constant coefficients are treated directly, including equality at the threshold. All derivative representatives are measurable and bounded globally. Finite sums preserve absolute continuity and the ae derivative, with no row independence assumption.

The interval-energy estimate follows from the fundamental theorem for absolutely continuous real functions and an explicit Cauchy--Schwarz argument obtained by integrating a square. Zero-length intervals are handled separately. The objective and derivative have proven finite bounds, giving every required MemLp and square-integrability fact. The final scalar theorem permits t=0 and all zero coefficients.

The retained command rebuilt both foundation modules and four named actual closures cleanly, each using only propext, Classical.choice and Quot.sound. Failed intermediate development logs remain retained. The selected multivariate IE22 target still requires the actual matrix-coordinate assembly, exact adjoint norm estimate, finite-product tensorization and literal stdGaussian transport. No full problem verification is claimed.
