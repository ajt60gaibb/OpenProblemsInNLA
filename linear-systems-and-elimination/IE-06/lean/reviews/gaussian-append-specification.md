# Gaussian append bound: independently approved contract before implementation

Scope: manuscript Lemma 4.5 (A5), using a fixed deterministic matrix and the actual iid standard Gaussian append law. This document was recorded before implementing GaussianCompression, RightInverseBounds, or GaussianAppend. Root independently approved the following exact argument and constants on 2026-10-06; the spectral agent independently checked the retained-inverse interface and owns its construction in TruncatedInverse. No manuscript probability estimate is assumed.

Let `1 ≤ k < n`, `M : Matrix (Fin n) (Fin n) ℝ`, `0 < μ`, `μ² ≤ k`, with zero-based `Spectral.singularValue M (n-k-1) ≥ μ` and `TruncatedInverse.sigmaInvSum M k ≤ 2*k*μ⁻²`. Append an actual `gaussianRect n (4*k)` matrix `G` to form `B=[M G]`. For `x>0`, let `C=2+98316*Real.exp 2`. The target is a simultaneous bound on the genuine Moore–Penrose inverse:

- `opNorm (pinv B)^2 ≤ C*μ⁻²*exp(2*x/k)`;
- `frobeniusSq (pinv B) ≤ C*k*μ⁻²*exp(2*x/k)`;
- the probability that either bound fails is at most `2*exp(-x)`.

This implies the manuscript's universal-constant form with exponent `C*x/k`, failure `3*exp(-x)`, and its narrower condition `x≥1`. No loss of a factor `k` in the operator bound is allowed. All norms are Euclidean operator/Frobenius norms and the inverse is the genuine spectral pseudoinverse, including singular inputs.

The deterministic retained decomposition supplies `R` and `U` with `UᴴU=I`, `MR=I-UUᴴ`, `RU=0`, `opNorm R≤μ⁻¹`, and `frobeniusSq R=sigmaInvSum M k`. No full-rank hypothesis on M is added. The finite positive left singular family is extended to an orthonormal basis on discarded zero directions; raw zero left-singular vectors cannot serve as columns of U.

The exact compression `X=UᴴG` has the actual `gaussianRect k (4*k)` law. This is proved from characteristic functions of standard Gaussian Euclidean vectors and the nested product law. No independence of `X` and `RG` is asserted or used. On the full-row-rank event for X, put `P=pinv X` and construct the right inverse `J=[R-RGPUᴴ; PUᴴ]` of B. The minimum-norm property of the Moore–Penrose inverse yields both norm bounds from J. If `L=opNorm(RG)` and `p=opNorm P`, exact estimates are

`opNorm J² ≤ 2*μ⁻² + 4*(1+L²)*p²`,

`frobeniusSq J ≤ 2*k*μ⁻² + k*(1+L²)*p²`.

The Frobenius cross term is zero: cyclic trace moves U next to R, where `RU=0`. The previously proved A2 gives `p²≤3*exp(2+x/k)/k` except on a set of probability `exp(-x)`. The approved original route used A1' at singular index zero. Before implementation, root also independently approved the simpler direct proved `GaussianOperatorNet.operator_net_tail_shift` on `GᵀRᵀ`: it gives `L²≤8*frobeniusSq R+16*(4*k*log 5+x)*opNorm R²≤(144*k+16*x)*μ⁻²≤8192*(k+x)*μ⁻²`, using `log 5≤2`, with the same failure bound. This avoids an unnecessary singular-value/operator-norm conversion and preserves the exact approved target and constants. Fixed transpose/compression pushforward identities transfer these bounds to the actual G law.

Because `μ²≤k`, `(1+8192*(k+x)*μ⁻²)/k≤8193*μ⁻²*(1+x/k)`. The elementary inequality `1+u≤exp u` for `u=x/k>0` gives the asserted C and exponent 2. A union bound gives failure 2; no conditional Gaussian selector or unproved independence is needed. Exceptional rank failures are removed using the proved Gaussian Gram positive-definiteness almost everywhere. The fixed transpose and compression maps are proved measurable. The conclusion bounds the outer measure of the exact actual pseudoinverse bad event using `Measure.le_map_apply` and almost-everywhere set inclusion, so no separate global pseudoinverse-measurability premise is needed. This stronger outer-measure form preserves the probability target. Choosing fixed deterministic R,U does not claim a globally measurable SVD selection.

Every local declaration must receive a LeanCert kernel trust audit. No `sorry`, native evaluation, new axiom, or assumed manuscript result is permitted in these supporting proof files. This contract is a mathematical specification, not a claim that implementation or the overall IE-06 proof is finished.
