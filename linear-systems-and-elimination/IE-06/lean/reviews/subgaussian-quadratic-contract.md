# Auxiliary subGaussian quadratic tail: exact preimplementation contract

This is a conditional auxiliary theorem for A4-min in the full proof specification. It does not assert that Gaussian restrictions to symmetric convex sets satisfy its hypothesis; deriving that fact still requires the Gaussian shift theorem.

Let $(\Omega,\mathcal F,\mu)$ be any probability space, let $a,b$ be arbitrary natural numbers (including zero), let $X:\Omega\to\mathbb R^a$ be measurable, and let $M\in\mathbb R^{a\times b}$ be deterministic. Assume, explicitly, that for every $v\in\mathbb R^a$, the random variable $\sum_i v_iX_i$ has Mathlib's HasSubgaussianMGF with parameter $\sum_i v_i^2$. This means that for every real $t$ its exponential moment is integrable and
$$
\int_\Omega \exp\!\left(t\sum_i v_iX_i(\omega)\right)d\mu(\omega)
\le \exp\!\left(\frac{t^2}2\sum_i v_i^2\right).
$$
No independence of the coordinates or of different projections is assumed. No source estimate is an axiom.

Define the squared Frobenius norm and squared projected Euclidean norm by the finite sums
$$
F^2=\sum_j\sum_i M_{ij}^2,\qquad Q(\omega)=\sum_j\left(\sum_i M_{ij}X_i(\omega)\right)^2.
$$
The planned conclusions are:
1. For a measurable scalar $Y$ with HasSubgaussianMGF parameter $1$, the function $\exp(Y^2/4)$ is integrable and its integral is at most $\sqrt2$.
2. When $F^2>0$, the function $\exp(Q/(4F^2))$ is integrable and its integral is at most $\sqrt2$, hence at most $\exp(1/2)$.
3. For every real $x\ge0$, including $F^2=0$, the ENNReal probability satisfies
$$
\mu\{Q>(2+4x)F^2\}\le\operatorname{ofReal}(\exp(-x)).
$$

For (1), Tonelli/Fubini and the standard Gaussian moment-generating formula give
$$
\int e^{Y^2/4}d\mu
=\int_{\mathbb R}\int_\Omega e^{zY/\sqrt2}d\mu\,d\gamma_1(z)
\le\int_{\mathbb R}e^{z^2/4}d\gamma_1(z)=\sqrt2.
$$
Integrability must be proved, not presumed in the interchange. For (2), use the actual column weights $w_j=(\sum_iM_{ij}^2)/F^2$, which are nonnegative and sum to one, and normalize each nonzero column by its Euclidean norm. Zero columns contribute zero weight and use the zero projection. Pointwise finite Jensen followed by integration gives the claimed moment bound. For (3), exponential Markov gives the factor $\sqrt2 e^{-1/2-x}\le e^{-x}$. If $F^2=0$, every entry of $M$ vanishes, hence $Q=0$ and the strict bad event is empty.

The proposed representation uses finite coordinate sums rather than an overloaded function-space norm, ensuring the norm is Euclidean and the matrix norm is Frobenius. The proof is symbolic: no numerical kernel certificate is needed beyond the elementary inequality $\sqrt2\le e^{1/2}$, which can follow from $1+u\le e^u$ at $u=1$ and squaring. Every exported declaration will have kernel trust and axiom checks.

## Approved equivalent implementation normalization, 2026-10-06 14:21 UTC

The implementation uses $Z\sim N(0,2)$ and $\exp(ZY/2)$, equivalently replacing the original standard-normal auxiliary variable by $\sqrt2$ times that variable. The Gaussian MGF then gives $\exp(Y^2/4)$, the directional MGF upper bound is $\exp(Z^2/8)$, and the density identity is
$$
\phi_2(z)\exp(z^2/8)=\sqrt2\,\phi_4(z).
$$
Independent mathematical review explicitly approved this equivalent normalization before the completed matrix proof was submitted. The root coordinator independently approved conclusions 1–3 and all zero-case guards before implementation. Actual column normalization and column weights are unchanged.
