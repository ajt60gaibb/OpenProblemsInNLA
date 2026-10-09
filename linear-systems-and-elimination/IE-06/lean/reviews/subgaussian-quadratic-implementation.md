# SubGaussianQuadratic implementation report

The module NLA/IE06/SubGaussianQuadratic.lean implements the exact independently reviewed auxiliary contract. Its SHA-256 is ba9231681db8d4e80e5cab9752b5cffe40c5af4fd28fdf2c368f89d256d7f4c6.

The probability measure, measurable vector, and all-direction HasSubgaussianMGF assumption are explicit theorem parameters. The assumption includes every real MGF parameter and its integrability; it is neither an axiom nor an asserted property of a Gaussian restriction. Coordinate independence is not assumed. Dimensions and matrices may be zero.

The scalar proof establishes joint integrability by dominating the integrated nonnegative integrand using its MGF bound, before invoking Fubini. The auxiliary law is N(0,2), with integrand exp(zY/2). A direct density identity with N(0,4) proves the exact square-exponential moment sqrt(2). All these steps are proved in Lean.

For the matrix bound, the code defines Euclidean squared norms and the squared Frobenius norm by finite sums, constructs the actual squared-column-norm weights, proves that their sum is one, and applies finite Jensen pointwise. The normalized directional MGF parameter is at most one; division by zero makes the zero column normalize to zero. A separate zero-column proof justifies the weighted square identity at that edge case. There is no hidden independence premise.

The final quadratic_tail theorem gives, for x at least zero, the ENNReal probability of the strict event
Q > (2+4x) F²
at most ofReal(exp(-x)). Exponential Markov uses sqrt(2) at most exp(1/2), proved from exp(1) at least 2. If F² is zero, the code proves every column is zero and the event is empty.

Validation on the pinned Lean and package cache completed with no compiler warnings. All 19 exported definitions and theorems passed LeanCert kernel trust assertions. Axiom reports contain only propext, Classical.choice, and Quot.sound. The local log is /private/tmp/ie06-subgaussian-check.log. This module proves the generic conditional A4-min quadratic consequence; the Gaussian convex-restriction premise and the complete IE-06 probabilistic proof remain unfinished.
