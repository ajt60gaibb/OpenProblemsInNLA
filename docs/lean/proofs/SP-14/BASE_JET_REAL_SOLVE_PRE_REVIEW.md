# SP-14 actual base-jet real solve: pre-proof contract

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen for independent mathematical review before Lean source. Fixed original Target: `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. Fixed source: `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, base Jacobian formula in Proposition “Odd-symbol pencil and its jets.” This is the **assembly** of the independently approved constructive base-pencil contract (SHA `bbcb1bfe...`) using the kernel-checked real matrix `BaseJetTriangular.lean` and the separately pre-reviewed actual `baseJetPolynomial_formula`. Implementation must wait for final approval of that polynomial formula and this contract.

## Exact actual real finite system

Fix `m q h : ℕ` with `2*q≤m+1` and `h≤q`. The bound implies `h≤m` except at `m=0`, where `h=q=0`. For a real vector `u : Fin h→ℝ`, pad it by zero to the `q` source variables and cast to complex:

```lean
noncomputable def baseJetPad (h q : ℕ) (hh : h ≤ q)
    (u : Fin h → ℝ) (d : Fin q) : ℂ :=
  if hd : d.val < h then (u ⟨d.val, hd⟩ : ℂ) else 0

noncomputable def baseJetRealMap (m q h : ℕ) (hh : h ≤ q)
    (u : Fin h → ℝ) (k : Fin h) : ℝ :=
  ((oddJetPolynomial
      (baseJetSymbol m q (baseJetPad h q hh u)) m).coeff k.val).re
```

The map uses the **actual** corrected circle symbol and the frozen `oddJetPolynomial`, hence the source's real polynomial equations. Prove the coefficient is real (imaginary part zero) and the exact identity, for every `u` and `k`,

\[
[t^k]R_{m,a_u}(t)
=\sum_{d=0}^{h-1}J^0_{kd}u_d,
\qquad J^0_{kd}=\begin{cases}-2(k+1)\binom{1/2}{d-k},&k\le d,\\0,&k>d.\end{cases}
\]

Equivalently, the public Lean theorem should state both the complex coefficient equality and `baseJetRealMap m q h hh = (baseJetMatrix h).mulVec` as functions. The proof uses the approved polynomial formula, the zero-padding index split, the real-to-complex half-binomial bridge, and the fact `k<h≤m` excludes the `X^m` coefficient. Handle `m=h=q=0` by the empty `Fin` eliminator, not an invalid positive-index argument.

## Explicit vector, uniqueness, and Jacobian

For any desired real first-`h` jet `y : Fin h→ℝ`, define **the actual source correction vector**

```lean
noncomputable def baseJetVector (m q h : ℕ)
    (hq : 2 * q ≤ m + 1) (hh : h ≤ q)
    (y : Fin h → ℝ) : Fin q → ℂ :=
  baseJetPad h q hh (baseJetSolve h y)
```

Prove, without existential vector or Jacobian premises,

```lean
theorem baseJetVector_spec ... (y : Fin h → ℝ) :
    ∀ k : Fin h,
      (oddJetPolynomial (baseJetSymbol m q (baseJetVector m q h hq hh y)) m).coeff k.val
        = (y k : ℂ)

theorem baseJetVector_zero_jet ... :
    JetVanishing (baseJetSymbol m q (baseJetVector m q h hq hh 0)) m h
```

The `y=0` solution is the base point and has a real vector; the arbitrary-target theorem is the substantive constructive right inverse. State uniqueness only among vectors supported on the first `h` coordinates (the zero-padding image). If `q>h`, the full `q`-variable equation system has a kernel, so asserting unique `v : Fin q→ℝ` would be false.

The source's regularity means the Jacobian of **these same real first-`h` coefficient equations** with respect to the selected first `h` variables has row rank `h`. The exact function equality `baseJetRealMap=J⁰.mulVec` gives the stronger finite difference identity `F(u')−F(u)=J⁰.mulVec(u'−u)` at every `u`; prove a formal `HasFDerivAt` or `fderiv` statement identifying its derivative with the continuous linear map of `baseJetMatrix h`, and use `baseJetMatrix_det_ne_zero` to conclude full rank. If a Mathlib derivative API forces a different representation, the public theorem must still identify the derivative of `baseJetRealMap` (not only an unrelated matrix) and prove its bijectivity; merely restating matrix invertibility is insufficient.

## Endpoints and remaining stage gap

At `h=0` the target and solve vectors are empty and unique in the selected coordinates; at `q=0` this is the only case. At `m=0` one has `q=h=0`, actual `T₁` characteristic polynomial `X`, and the empty Jacobian has rank zero. At `m=1,q=h=1`, the real equation is `F(v)=-2v`, so `v=-y/2`. At `m=3,q=h=2`, `F(v)=(-2v₀-v₁,-4v₁)`, with determinant `8` and an explicit unique real solve. These checks use the actual restored packet, whose `K_m` term alone is invisible to the selected section.

This theorem establishes **base-model** finite vector existence and regularity for every allowed `m,q,h`. It does not solve the source's stages after positive and earlier restored packets are present. Those require the separately identified all-background stage gate, analytic right-inverse and forcing estimates, nonlinear contraction, norm budgets, two-sided nonextension, and final empirical/canonical gap. No final `Target` follows here.
