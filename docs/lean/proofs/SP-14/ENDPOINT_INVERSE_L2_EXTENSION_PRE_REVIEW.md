# SP-14: finite triangular inverse and its actual L² extension

**Status:** frozen mathematical, numerical, and indexing pre-implementation contract for independent review. **Author:** `/root/sp14_base_proof`, 10 October 2026. No Lean source for this gate has been written.

## Source locks and scope

| Source | SHA-256 |
| --- | --- |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Canonical `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, Lemma “The square-root extension of the analytic projection,” lines 856–902 | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| `BaseJetBinomialInverse.lean` | `362a891068b132248f388bf364908f6a7350fa3f7d226debfb658e3847db3e47` |
| `EndpointAbsoluteKernel.lean` | `da1aad945e27098c98daefddeacad99ad0246eb8a61890953317edfa05b2b673` |
| `EndpointExtensionKernel.lean` | `2dd8c29d8d8ac936344e86ef37dcd794443113b3c4bf7c3f72268a8d8a59e83c` |
| `EndpointFiniteRealizationPositive.lean` | `427e677daa825ed665935c7e72e59300be85235f9947e14f82f70ed2859a1b91` |
| `EndpointFiniteRealizationPointwise.lean` | `60dd3e510970fcc241ab2f535a987d53cd642f936f9daef0ad41b37cc4d0b6b1` |
| `WeightedSobolevPhysical.lean` | `ea0166080ec91c5df4da14e2f38eca5fc2a7f9271866099aad1fb8f46e5ba109` |

The source's endpoint-extension lemma has an additional statement beyond the already audited two-sided extension and endpoint zero: the finite triangular inverse `V=T(g₀)⁻¹y` extends with `‖V‖_{L²} ≤ C_r‖y‖_{H^r}` when `r>1/2`. This contract treats that **actual inverse**, starting from the frozen `endpointFiniteInverse`, and proposes the explicit sufficient constant `B_r=1+1/(r-1/2)`. It does not alter the definition of `endpointCircleRealization`, assume pointwise values for an arbitrary `L²` limit, or claim the final negative `Target`.

## Exact index and normalization definitions

Write `b_l=baseInverseCoeff l=(-1)^l A_l`, where `A_l=endpointCentralCoeff l=binom(2l,l)/4^l>0`. The audited `endpointCentralCoeff_sq_bound` says `(l+1)A_l²≤1`. Let `a_k=physicalCoeff r y k=(k+1)^(-r)y_k` and let `T_N=sobolevTruncation r N`. The frozen finite inverse is

\[
V_N(z)=\sum_{k=0}^{N-1}a_k\sum_{l=0}^{k}b_l z^{k-l}.
\]

For `d≥0` its analytic Fourier coefficient is the **upper-triangular** sum

\[
v_{N,d}=\begin{cases}\displaystyle\sum_{k=d}^{N-1}b_{k-d}a_k,&d<N,\\0,&d\ge N.\end{cases}
\]

In Lean, define `endpointFiniteInverseCoeff (r : ℝ) (y : SobolevCoeff r) (N d : ℕ) : ℂ` by `∑ k ∈ Finset.Ico d N, (baseInverseCoeff (k-d) : ℂ) * physicalCoeff r y k`. The `Finset.Ico` is empty when `d≥N`, including `N=0`. The coefficient of `z^d` in the frozen `endpointFiniteInverse r y N` must equal this exact expression, with no reversal of `d` and `k`. At `N=1`, `v_0=a_0`. At `N=2`, `(v_0,v_1)=(a_0-a_1/2,a_1)`; at `N=3`, `(v_0,v_1,v_2)=(a_0-a_1/2+3a_2/8,a_1-a_2/2,a_2)`.

Define the nonnegative Hilbert–Schmidt scalar

\[
S_r=\sum_{k=0}^{\infty}(k+1)^{-2r}\sum_{l=0}^{k}A_l^2,
\qquad B_r=1+\frac1{r-1/2}.
\]

Proposed Lean names/signatures (split into separate frozen modules and final audits if useful):

```lean
noncomputable def endpointFiniteInverseCoeff (r : ℝ)
    (y : SobolevCoeff r) (N d : ℕ) : ℂ :=
  ∑ k ∈ Finset.Ico d N,
    (baseInverseCoeff (k - d) : ℂ) * physicalCoeff r y k

noncomputable def endpointInverseHSColumn (r : ℝ) (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ) ^ (-2 * r)) *
    ∑ l ∈ Finset.range (k + 1), endpointCentralCoeff l ^ 2

noncomputable def endpointInverseHSSquare (r : ℝ) : ℝ :=
  ∑' k : ℕ, endpointInverseHSColumn r k

noncomputable def endpointInverseHSBound (r : ℝ) : ℝ :=
  1 + 1 / (r - 1 / 2)

theorem summable_endpointInverseHSColumn (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) :
    Summable (endpointInverseHSColumn r)

theorem endpointInverseHSSquare_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) :
    endpointInverseHSSquare r ≤ endpointInverseHSBound r ^ 2

theorem endpointFiniteInverse_coeff (r : ℝ) (y : SobolevCoeff r)
    (N d : ℕ) :
    FourierCoefficient (endpointFiniteInverse r y N) (d : ℤ) =
      endpointFiniteInverseCoeff r y N d

theorem endpointFiniteInverse_fourier_neg (r : ℝ)
    (y : SobolevCoeff r) (N t : ℕ) :
    FourierCoefficient (endpointFiniteInverse r y N)
      (-((t + 1 : ℕ) : ℤ)) = 0

theorem endpointFiniteInverse_coeff_energy_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) (N : ℕ) :
    (∑ d ∈ Finset.range N, ‖endpointFiniteInverseCoeff r y N d‖ ^ 2) ≤
      endpointInverseHSSquare r * ‖y‖ ^ 2
```

The Fourier theorem uses the **frozen normalized integral** `FourierCoefficient`, not a new coefficient extractor. A separate exact Parseval bridge must prove

\[
\frac1{2\pi}\int_{0}^{2\pi}
 |V_N(\exp(it))|^2\,dt
 =\sum_{d=0}^{N-1}|v_{N,d}|^2.
\]

The integral is the ordinary real interval integral of the continuous real integrand, so no totalized-integral additivity issue arises. It is the normalized Haar `L²(\mathbb T)` norm squared. The bound above gives `‖V_N‖_{L²}≤B_r‖y‖` for every `N`, including `N=0`, and also `‖V_N(y)-V_N(x)‖_{L²}≤B_r‖y-x‖` by complex linearity.

For the actual extension, use `T_N y→y` in the frozen `SobolevCoeff r=lp ℂ 2` norm. The finite inverse of `T_N y` is the same polynomial `V_N(y)`. For `N≥M`, finite triangular compatibility gives `V_M(y)=V_N(T_M y)`, and therefore `‖V_N(y)-V_M(y)‖₂≤B_r‖y-T_M y‖`. Completeness gives a unique normalized-circle `L²` limit `V(y)`, complex linear and bounded by `B_r`. Equivalently, its nonnegative Fourier coordinates form an `lp ℂ 2` vector with exact coordinate formula

\[
v_d=\sum_{k=d}^{\infty}b_{k-d}(k+1)^{-r}y_k,
\]

where each row sum is absolutely convergent by Cauchy–Schwarz. The negative Fourier coordinates are zero. Any public operator theorem must identify this coordinate model with the actual normalized circle `L²` limit; merely producing an abstract `lp` map does not by itself complete the source's `L²` assertion. The eventual Lean signature for that `Lp` map must name the pinned normalized circle measure and be separately pre-reviewed if it cannot be fixed in this contract without a definitional mismatch.

## Exact scalar proof and numerical checks

Set `δ=r-1/2>0`. The audited coefficient estimate gives `A_l²≤1/(l+1)`, hence

\[
\sum_{l=0}^{k}A_l^2\le H_{k+1}\le 1+\log(k+1)
 \le (1+1/\delta)(k+1)^\delta.
\]

The last inequality follows from `log x≤(x^δ−1)/δ` for `x≥1` and `x^δ≥1`. Consequently

\[
S_r\le B_r\sum_{n=1}^{\infty}n^{-(1+\delta)}
 \le B_r(1+1/\delta)=B_r^2,
\]

using the decreasing-integral bound for the p-series. This proves summability for **every** real `r>1/2`, with no auxiliary assumption `r<1`. At `r=3/4`, `δ=1/4`, `B_r=5`, so `S_r≤25`. At `r=7/8`, `δ=3/8`, `B_r=11/3`, so `S_r≤121/9`. The exact first column-energy inner sums are `1`, `5/4`, `89/64`, and `381/256` for `k=0,1,2,3`, respectively. These rational values were computed from `A_0=1`, `A_1=1/2`, `A_2=3/8`, `A_3=5/16`; they check the triangular orientation and the `k=0` endpoint.

For the finite coefficient-energy estimate, write `M_{d,k}=b_{k-d}(k+1)^{-r}` when `0≤d≤k<N`, and zero otherwise. Rowwise Cauchy–Schwarz yields `|v_{N,d}|²≤(∑_{k<N}|M_{d,k}|²)(∑_{k<N}|y_k|²)`. Sum over `d<N`, exchange the finite nonnegative sums, and use `∑_{k<N}|y_k|²≤‖y‖²` and `∑_{d≤k}|M_{d,k}|²=(k+1)^(-2r)∑_{l≤k}A_l²`. This gives the displayed inequality with the **actual** `S_r`, including the empty `N=0` case. Finite Fourier orthogonality then gives Parseval; there is no unproved infinite interchange in this first stage.

This gate leaves the perturbed Cauchy projection inverse, its compatible two-level bounds, nonlinear jet existence, both-sided nonextension of the packet symbol, selected-section multiplicity construction, canonical gap, and the frozen negative `Target` open. Do not use the base symbol itself as the final counterexample.
