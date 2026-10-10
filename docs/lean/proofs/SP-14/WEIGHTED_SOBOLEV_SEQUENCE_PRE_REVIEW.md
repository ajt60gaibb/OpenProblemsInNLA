# SP-14: literal weighted coefficient-sequence Sobolev spaces

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen mathematical pre-proof contract; no Lean implementation is authorized until independent mathematical review. The unchanged target is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The canonical source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, Lemma “Oversampling from two Sobolev bounds” and proof (lines 1780–1806). The approved abstract operator theorem is `lean-statements/NLA/Proofs/SP14/SobolevOversampling.lean`, frozen SHA-256 `fd9b5a433847dc8392070752a97244bebeedde08d4d7f7a198e24d64f6f27d77`. This contract supplies its concrete sequence-space geometry only.

## Exact spaces and norm convention

For every real `s`, let `H^s` consist of **complex coefficient sequences** `a : ℕ → ℂ` with finite energy

\[
  \|a\|_s^2
  =\sum_{n=0}^{\infty}(n+1)^{2s}|a_n|^2<\infty.
\]

The exponent is the real power, and `|a_n|` is the complex norm. The square root of this nonnegative sum is the norm. The index starts at `n=0`, so the constant coefficient has weight one. The expression is meaningful for every `s∈ℝ`, including negative `s`.

An implementation may use Mathlib's complete `lp (fun _ : ℕ => ℂ) 2` as the normed carrier, **only with an explicit isometric identification of its elements with the above coefficient sequences**: for `y∈ℓ²`, set

\[
  \operatorname{coeff}_s(y)_n=(n+1)^{-s}y_n.
\]

Prove that `coeff_s` is a complex-linear bijection onto precisely the finite-energy sequences, with inverse `a↦((n+1)^s a_n)_n`, and prove the exact norm-square formula above (equivalently `‖y‖²=∑‖y_n‖²`). A phantom `s` parameter on an unweighted `ℓ²` carrier without this coefficient identification and equality does **not** meet the contract. Alternatively, use the finite-energy subtype directly and transfer the normed-space and completeness structures through this isometry. In either realization, every public coordinate formula below refers to `coeff_s` and therefore to the actual coefficients.

## Exact maps and public conclusions

Fix `s∈ℝ`, `τ>0`, and `r=s+τ`. For `q,h∈ℕ`, the required continuous complex-linear maps are:

* Inclusion `ι_{r,s}:H^r→H^s`, with `coeff_s(ιx)_n=coeff_r(x)_n` for every `n`. In weighted `ℓ²` coordinates this is diagonal multiplication by `(n+1)^{-τ}`; prove `‖ι‖≤1`.
* Truncation `P_n:H^s→H^s`, with `coeff_s(P_nx)_k=if k<n then coeff_s(x)_k else 0`. Prove `P_n²=P_n`, `‖P_n‖≤1`, and `P_0=0`. Thus `P_n` retains exactly coefficients of degree `<n`.
* Finite-band lift `L_h:H^s→H^r`, with `coeff_r(L_hy)_k=if k<h then coeff_s(y)_k else 0`. In weighted `ℓ²` coordinates this is diagonal multiplication by `(k+1)^τ` on `k<h` and zero elsewhere. Prove `ι L_h=P_h`, including `L_0=0`.

The two exact numerical estimates required for the abstract theorem are, **for all** `x∈H^r`, `y∈H^s`, `q,h∈ℕ`:

\[
 \|(I-P_q)\iota x\|_s\le(q+1)^{-\tau}\|x\|_r,
 \qquad
 \|L_hy\|_r\le h^\tau\|P_hy\|_s.
\]

Here `0^τ=0` because `τ>0`, and the `h=0` inequality is `0≤0`. The bounds may be proved by squaring nonnegative norms and comparing each summand. At `k≥q`, `(k+1)^{-2τ}≤(q+1)^{-2τ}`. At `k<h` with `h>0`, `(k+1)^{2τ}≤h^{2τ}`. These are exactly the source's factors; replacing `q+1` with `q`, or `h` with `h+1`, changes the theorem.

The intended standalone Lean interface exports `SobolevCoeff (s : ℝ)`, its actual coefficient map and isometric finite-energy identification, `sobolevInclusion s τ`, `sobolevTruncation s n`, and `sobolevFiniteLift s τ h`, plus named theorems for the coordinate formulas, `P_n²=P_n`, the two operator-norm bounds, `P_0=L_0=0`, `ι L_h=P_h`, and the two displayed pointwise estimates. The type of each map must be `ContinuousLinearMap ℂ` between the specified complete normed spaces. Exact Lean names may be refined before source work, but the mathematical content and all index endpoints may not be weakened. The previously approved abstract `sobolevOversampling` theorem can then be instantiated **only after** the compatible `A_s,A_r,B_s,B_r` and their numerical operator bounds are separately proved for the actual background.

## Endpoint and independent numerical checks

Take `s=0`, `τ=1`, and the finite coefficient sequence `a=(1,2,3,0,…)`. Its squared `H^0` and `H^1` norms are `14` and `98`. At `h=2`, `‖L_2a‖_1²=1+16=17≤2²(1+4)=20`; the lift retains exactly `(1,2)`. At `q=2`, the tail of inclusion has squared `H^0` norm `9`, while `(q+1)^{-2}‖a‖_1²=98/9`, so the bound holds. The single mode at `k=q=2` gives equality `9=3^{-2}·81`, confirming the sharp `q+1` index. The single mode at `k=h-1=1` gives equality in the lift estimate, confirming the sharp `h` index. At `h=0`, both `P_0` and `L_0` vanish and `0^τ=0`; at `q=0`, the tail factor is one. No finite-dimensional test substitutes for the all-sequence proof.

## Feasibility and remaining obligations

The `lp` realization provides completeness and a native complex normed-space structure. The work in this gate is an explicit diagonal-multiplier construction on `ℓ²` and summandwise norm comparisons, plus the exact isometric identification; this is larger than the already checked abstract algebra and may be implemented incrementally as separately reviewed modules. It must never be reported as a proof of compatible inverses or their bounds for the source's background-dependent operator `\mathcal A_g`. The forcing estimate, nonlinear contraction, norm budgets, both-sided nonextension, canonical spectral gap, and frozen negative `Target` remain open.
