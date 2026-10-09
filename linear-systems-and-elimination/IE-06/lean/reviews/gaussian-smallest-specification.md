# Gaussian smallest-singular-value work: approved radial building blocks

Before implementation, the root reviewer approved the exact claims (a)–(c)
on 2026-10-06. These are unconditional building blocks, not an A2 proof.

(a) For E_d = EuclideanSpace ℝ (Fin d), the standard Gaussian measure has
Lebesgue density `(sqrt(2*pi)^d)⁻¹ * exp(-‖z‖²/2)`, with the volume normalization
proved by the orthonormal coordinate isometry.

(b) Under the literal product standard normal law, put `S_d(z)=∑i z_i²`.
For all natural d,q the function S_d^q is integrable and its integral is
`∏ j in range q, ((d:ℝ)+2*j)`. This includes d=0 and q=0.

(c) For natural d,q with 2*q<d, the function `(S_d^q)⁻¹` is integrable and its
integral is `(∏ j in range q, ((d:ℝ)-2*(j+1)))⁻¹`. Every denominator factor is
strictly positive. If q=0 the integrand and empty product are both1. If q>0 the
Lean inverse at the origin is0; the origin has measure0 under the hypothesis.

The approved proof uses Euclidean radial Haar integration, scalar Gamma
integrals, the Gamma recurrence, and exact Gaussian normalization. Local
AI-assisted RRF GaussianDensity/GaussianRadial sources provide prior supporting
proof structure, adapted only with attribution and exact provenance hashes in
source/gaussian-smallest-provenance.json. No RRF module/axiom is imported.

The separately approved future route to A2 defines the actual rectangular
Moore–Penrose inverse as `Gᴴ * cfc (fun t:ℝ => t⁻¹) (G*Gᴴ)`. For positive r,
m≤r and n≥3r, a directional inverse Gram moment and independent Gaussian
probe give

`E[‖G†‖op^(2*r)] ≤ (3*exp(2)/r)^r`.

Markov would then give the unchanged /r scaling with universal constant3,
threshold `3*exp(2+x/r)/r`, probability at most exp(-x). This is stronger in x
than the source's `2*x/r` exponent, but uses3 instead of2. The root explicitly
approved the universal constant adjustment as absorbable in the final
unspecified C; it does not introduce a factor depending on r. The conditional
Gaussian regression, true pseudoinverse algebra, and A2 moment/tail bounds
remain distinct tasks and are not assumed by (a)–(c).
