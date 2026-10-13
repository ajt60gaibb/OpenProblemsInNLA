# SP-14: exterior-factor boundary and finite Laurent background algebra

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** source-locked mathematical/numerical pre-implementation contract; no Lean source for this gate. Frozen negative target: `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. Canonical source: `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, source lines 45–72. Reviewed prerequisites: `BaseCoefficient.lean` SHA `63dcd98bb3a45e77b2b0fd2644d444f9cfe866fb9dae5535d1b7cd1f73081bf4`, `BaseCoeffSummable.lean` SHA `1da659ff573ddee8d598d32150fec45f7ae5d5eb023c2a9277a0500547ad9892`, `BaseExteriorSeries.lean` SHA `8e19c9af8809fc44414b90696a089d32417934475adc95f58aafa6db5b83dd0d`, and `BaseExteriorBoundarySquare.lean` SHA `93b81c168bf831439928020397bb14985f9fe26de2060e50c2c55a535c9e6239`.

## Normalized exterior factor on the circle

The source takes the exterior branch `g₀(s)=√(1+s⁻¹)` normalized to `1` at infinity. Its already reviewed coefficients are `c_n=binom(1/2,n)`, with `c₀=1`, `c₁=1/2`, `c₂=−1/8`, `c₃=1/16`, and `∑‖c_n‖<∞`. Define its **boundary factor**, rather than an arbitrary square-root choice, by the exact series

\[
 g_{0,\partial}(s)=\sum_{n=0}^{\infty}c_n s^{-n},\qquad s\in\mathbb T.
\]

The intended Lean name is `baseExteriorFactor (s : Circle) : ℂ`. The following unconditional theorems are the first implementation gate, with no excluded circle point:

```lean
theorem summable_baseExteriorFactor_terms (s : Circle) :
  Summable (fun n : ℕ => baseCoeff n * (s : ℂ) ^ (-(n : ℤ)))

theorem continuous_baseExteriorFactor : Continuous baseExteriorFactor

theorem baseExteriorFactor_sq (s : Circle) :
  baseExteriorFactor s ^ 2 = 1 + (s : ℂ)⁻¹

theorem baseExteriorFactor_at_neg_one :
  baseExteriorFactor (-1 : Circle) = 0

theorem baseExteriorSymbol_factor (z : Circle) :
  baseExteriorSymbol z = (z : ℂ) * baseExteriorFactor (z ^ 2)
```

The square follows by the absolute Cauchy product and the exact reviewed convolution `c*c=1+X`: at `n=0` the coefficient is `1`, at `n=1` it is `1`, and every higher coefficient is `0`. The circle nonzero property justifies negative powers. At `s=-1`, the square is `1+(-1)⁻¹=0`, hence the boundary factor is exactly zero; there is no division by the factor there. For the `z` identity, `(z²)^{-n}=z^{-2n}` and multiplication by `z` gives the existing exponent `1−2n` term by term. This fixes the branch through the *specific normalized coefficient series*. The formal exterior series has constant coefficient `1`; this contract does not yet claim a Lean holomorphic extension to `|s|>1` or prove its limit at infinity.

## Finite real Laurent background and exact curve algebra

For `u,v : ℕ`, real coefficient vectors `p⁻ : Fin u → ℝ`, `p⁺ : Fin v → ℝ`, and `s : Circle`, define

\[
 P_-(s)=\sum_{j=0}^{u-1}p^-_j s^{-(j+1)},\qquad
 P_+(s)=\sum_{j=0}^{v-1}p^+_j s^{j+1},\qquad P=P_-+P_+.
\]

Thus the negative powers are **strictly** negative, the positive powers are **strictly** positive, and the empty vectors give zero polynomials. Define the actual finite-background boundary objects

\[
 g(s)=g_{0,\partial}(s)+P(s),\qquad h(s)=s g(s)^2-1,\qquad
 a(z)=z g(z^2).
\]

The second implementation gate should expose definitions `negativeLaurent`, `positiveLaurent`, `finiteBackgroundFactor`, `finiteBackgroundCurve`, and `finiteBackgroundSymbol`, together with these unconditional identities and continuity statements:

\[
 h(s)-s=2s\,g_{0,\partial}(s)P(s)+sP(s)^2,
 \qquad
 a(z)=a_0(z)+zP_-(z^2)+zP_+(z^2),
\]

where `a₀=baseExteriorSymbol`, using the first gate's factor theorem. All five functions are continuous for every finite real vector, including `u=v=0`. For the source's **separate** contact premises `P_-(-1)=0` and `P_+(-1)=0`, prove `g(-1)=0` and `h(-1)=-1`; the conclusion may not be inferred from `P_-(-1)+P_+(-1)=0` alone. When `u=v=0`, prove `g=g₀`, `h(s)=s` and `a=a₀` pointwise. As a nonempty exact endpoint check, `p^-_0=p^-_1=t`, `p^+_0=p^+_1=r` give `P_-(s)=t(s^{-1}+s^{-2})` and `P_+(s)=r(s+s²)`, each zero at `s=-1`; the same `h(-1)=-1` follows for all real `t,r`. No floating-point approximation or choice of a square-root sign is involved.

The public Lean signatures may package the coefficient vectors into a structure, but must retain the finite real Laurent formulas, separate endpoint premises, exact `Circle`/`ℂ` coercions, and the displayed identities for **all** lengths, including `0`.

## Limits of this gate

This establishes the source's actual boundary `g`, `h`, and symbol `a` as algebraic/continuous objects. It does not establish the five strict Wiener smallness inequalities, Jordan curve, conformal map, exact limiting Jacobian, compatible inverse maps on `H^{-1/4}` and `H^{-1/8}`, or the `2^100` bounds in the approved actual-background oversampling contract SHA `5b52aaf4103ac675f74797cbd17ba63c39fdca5556b5203076c15a5cd889db68`. The exterior holomorphy/normalization at infinity also remains a separate analytic proof. Nonlinear packet existence, both-sided nonextension, canonical gap, and the original negative Target remain open. Each Lean source module must be frozen unimported and receive its own final source/signature/kernel audit after this mathematical pre-review.
