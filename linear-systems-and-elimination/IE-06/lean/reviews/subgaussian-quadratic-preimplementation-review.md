# Independent review of the subGaussian quadratic contract

Reviewed contract SHA-256: `5fb7efc54d528e199a8da82029907785c2ebdf13b2f0675aec68d10b0564724d`. Reviewer: independent mathematical-review agent, before implementation. Verdict: approved.

The exact hypotheses are a probability measure, measurable finite-dimensional X, and directional HasSubgaussianMGF with variance proxy the squared Euclidean norm of the direction. No independence of coordinates or column projections is necessary. The auxiliary-Gaussian identity uses zY/√2, giving exp(Y²/4); Tonelli must precede the integrability conclusion. The scalar bound is √2. Actual squared column norms divided by F² are nonnegative weights summing to one; zero columns have zero weight, and finite convexity then gives the desired moment bound. Exponential Markov at (2+4x)F² is valid for x≥0 because √2 exp(−1/2)≤1. If F²=0 every matrix entry and Q vanish, so the strict exceedance event is empty, including all zero-dimensional cases.

Gaussian convex restrictions satisfying the directional MGF hypothesis remain a separate substantive proof obligation. This conditional auxiliary statement must not be reported as proving that missing input.
