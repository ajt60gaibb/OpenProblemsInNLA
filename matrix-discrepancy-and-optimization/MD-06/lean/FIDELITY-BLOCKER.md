# Fidelity and blocker record

The source theorem quantifies over uniform labelled simple 3-regular graphs on every even `n >= 4`, with energy
`sum_{ {u,v} in E } (1 - cos(theta_u - theta_v))` on `(R / 2*pi Z)^n`. It concludes that the probability that all local minima are synchronized tends to zero. It also concludes that the probability tends to one of a nonsynchronized critical point whose edge cosines exceed `1/32` and whose Hessian quadratic form is at least `(1/320) * ||z||^2` on the all-ones orthogonal complement.

The approved specification additionally records the correction lemma (gap `gamma`, cosine lower bound `c`, gradient threshold `c^2*gamma/(4*sqrt 2)`, correction radius `c/(2*sqrt 2)`, final cosine `c/2`, Hessian lower bound `c*gamma/2`) and the cycle/tree constants (`ell` a positive multiple of four, `R >= 4`, `gamma = 1/10`, `c_0 = sqrt(1-t_4^2) > 1/16`, `F_R`, `t_R`, `delta_j`, `a_j`, and `R = 29 + ceil(log_2 ell)`). These are retained in `../MD-06/SPEC.md`; they are not silently weakened in the Lean Challenge.

## Exact blocker

The pinned Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474` is now available in the shared cache and the core-only files have been rerun against it. LeanCert revision `621a43d7cf21f87872392a01e874f2f1dbddc926` and Lean Comparator remain unavailable, and network access is blocked. Lean core has no real-number, torus, finite-probability, graph-spectrum, or random-regular-graph libraries. The semantic interface therefore records those objects as contracts. `Solution.lean` cannot claim the complete result without introducing unproved custom axioms, which is prohibited.

