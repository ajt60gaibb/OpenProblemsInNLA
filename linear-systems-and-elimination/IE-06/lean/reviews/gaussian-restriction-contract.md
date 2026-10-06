# Exact centered Gaussian restriction contract

For every natural dimension n and measurable convex centrally symmetric K in real coordinate space, let mu be the concrete independent standard Gaussian product law gaussianVector n. Assume mu(K) is nonzero and define nu = mu(K)^(-1) times mu restricted to K. The planned conclusions are unconditional theorems with these geometric hypotheses: nu is a probability measure, and for every v and real t, exp(t*sum_i v_i*x_i) is nu-integrable and has expectation at most exp(t²*sum_i v_i²/2). This yields DirectionalSubGaussian nu id and the exact previously reviewed quadratic_tail conclusion under nu.

The proof uses the completed GaussianShift.gaussian_shift_le theorem, whose input is measurability, convexity and symmetry rather than an assumed shift inequality. Completing the square gives the exact intermediate identity
$$
\int_K \exp(t\langle v,x\rangle)d\mu(x)
=\exp(t^2\|v\|_2^2/2)\mu\{y:y+tv\in K\}.
$$
The nonnegative integral identity is proved by translation of Lebesgue measure and the already verified Gaussian density bridge. Integrability comes independently from the full Gaussian linear MGF restricted to K and finite rescaling. The shift theorem bounds the shifted mass by mu(K), after which positive finite normalization cancels. Dimension zero and zero directions require no exception; the positive-mass hypothesis excludes only undefined normalization.

This is the original reviewed A4-min restriction premise, now to be proved from the adopted Prékopa–Leindler kernel proof, and not an additional axiom.
