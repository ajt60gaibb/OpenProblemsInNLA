# SP-14: finite polynomial consistency of the actual endpoint circle realization

**Status:** source-locked mathematical and exact-rational numerical pre-implementation contract; no Lean source for this gate before independent review. **Author:** `/root/sp14_base_proof`, 10 October 2026.

The frozen negative Target is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The canonical construction is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, Lemma “The square-root extension of the analytic projection” at lines 851–900. The exact Fourier normalization/sign and `Toeplitz` row-minus-column convention remain those of the frozen `Statements/SP14.lean`; no statement or identity file is changed.

The independently audited prerequisites are `EndpointBaseSeries.lean` (the exterior normalized `g₀(s)=√(1+s⁻¹)` circle branch), `EndpointExtensionKernel.lean` (negative integral for each inverse monomial), `EndpointExtensionPositive.lean` (nonnegative integral for each inverse monomial), `EndpointNegativeOperator.lean` (actual weighted negative Fourier CLM), `EndpointCircleFourier.lean` (both actual Fourier branches of the realized circle series), and `EndpointCircleEnergy.lean` (conventional full-circle Sobolev energy). The exact imported-source hashes should be recorded by final review; this contract uses their public statements rather than replacing them with formal Laurent coefficients.

## Exact mathematical statement

Fix `1/2<r<1`, `y : SobolevCoeff r`, and a natural cutoff `N`, with **finite support** `∀ k : ℕ, N ≤ k → y k = 0`. Let `a_k=physicalCoeff r y k`. The canonical triangular inverse polynomial on the circle is

\[
 V_N(y,z)=\sum_{k=0}^{N-1}a_k\,\texttt{endpointInverseMonomial}(k,z).
\]

It is a polynomial in nonnegative powers of `z`; the monomial inverse is exactly the previously reviewed `∑_{l=0}^k baseInverseCoeff(l) z^{k-l}`. Define the canonical finite endpoint extension as `E_N(y,z)=endpointBaseSymbol(z)·V_N(y,z)`. The required public Lean theorem is the **pointwise equality of genuine continuous circle functions**

```lean
noncomputable def endpointFiniteInverse
    (r : ℝ) (y : SobolevCoeff r) (N : ℕ) (z : Circle) : ℂ :=
  ∑ k ∈ Finset.range N,
    physicalCoeff r y k * endpointInverseMonomial k z

theorem endpointCircleRealization_eq_finiteInverse
    (r : ℝ) (hrHalf : (1/2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (N : ℕ)
    (hy : ∀ k : ℕ, N ≤ k → y k = 0) (z : Circle) :
    endpointCircleRealization r hrHalf hr1 y z =
      endpointBaseSymbol z * endpointFiniteInverse r y N z
```

If the exact equality is staged through Fourier coefficients, expose the intermediate two-sided integral identities for every `k,t : ℕ`:

```lean
FourierCoefficient (fun z => endpointBaseSymbol z * endpointFiniteInverse r y N z)
  (k : ℤ) = physicalCoeff r y k

FourierCoefficient (fun z => endpointBaseSymbol z * endpointFiniteInverse r y N z)
  (-((t+1 : ℕ) : ℤ)) =
    physicalCoeff r (endpointNegativeOperator r (by linarith) hr1 y) t
```

The first is finite linearity plus `endpointExtension_fourier_nonneg`: for `k<N`, only its own monomial contributes, and for `k≥N`, the support condition makes `physicalCoeff r y k=0`. The second is finite linearity plus `endpointExtension_fourier_neg` with `j=t+1`, followed by the exact `endpointNegativeOperator_apply` infinite row `tsum` reduced to `range N` using `hy`. The weighted matrix entry is `(t+1)^r(k+1)^{-r}` times the *actual frozen Fourier coefficient*; multiplying by `y_k` and returning to physical coordinates cancels those two weights. This cancellation must be proved, not assumed by naming a matrix.

The continuous-function equality follows from equality of every integer Fourier coefficient and Fourier uniqueness for continuous circle functions, or from a directly proved absolutely convergent Laurent expansion. The chosen Lean uniqueness result must be reconciled with `FourierCoefficient`'s literal real-interval integral `1/(2π)∫₀^{2π} f(Circle.exp t)e^{-ipt}dt`; no abstract Fourier functional is an acceptable substitute without an exact equivalence theorem. The two branches `k≥0` and `-(t+1)<0` exhaust `ℤ`, including `k=0` and `t=0` without overlap. Continuity of the finite source function follows from continuity of `endpointBaseSymbol` and each finite inverse monomial; continuity of the realization is already audited.

## Exact endpoint and numerical checks

For `N=0`, the support hypothesis forces `y=0`; the finite sum is empty, and both sides are zero. For the unit physical coefficient at `k=0` with all other coefficients zero, `V=1`, so `E=g₀`; its Fourier coefficients at `0,-1,-2` are exactly `1,1/2,-1/8`. For the unit physical coefficient at `k=1`, `V=z-1/2`; its Fourier coefficients at `1,0,-1,-2` are exactly `1,0,-3/8,1/8`. These follow from `g₀(z)=1+(1/2)z⁻¹-(1/8)z⁻²+(1/16)z⁻³+…`, and the negative values agree with the reviewed kernel at `j=1,2`. They check the `j=t+1` reversal and sign; they are not floating-point approximations. For a weighted basis input, use `y_k=(k+1)^r`; the displayed physical examples are recovered exactly after the weight cancellation.

The gate establishes the manuscript's formula `Ey=g₀V` **only for finite inputs**. It does not yet prove `endpointBaseSymbol(-1)=0`, pointwise vanishing of the infinite extension, an `L²` bound for `V`, the source's all-`0<r<1` function-space extension, the perturbed background operator, compatible inverses, nonlinear stage, jet-vector existence, both-sided nonextension, canonical gap, or the frozen negative Target. Each remains a separate mathematical and Lean obligation. Keep all existing Targets and published problem identities fixed. After independent mathematical/numerical pre-review, implement in an unimported file, freeze its SHA, and require separate imported LeanCert source/signature/kernel audit before aggregate import.
