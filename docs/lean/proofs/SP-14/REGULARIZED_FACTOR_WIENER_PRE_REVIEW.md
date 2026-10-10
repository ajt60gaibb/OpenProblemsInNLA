# SP-14: literal weighted Wiener size of the regularized exterior factor

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen mathematical and numerical pre-implementation contract. Frozen negative target: `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. Canonical source: `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, especially the weighted Wiener norm at lines 62–67 and endpoint cancellation at lines 765–785. Parent mathematical contract `ENDPOINT_WIENER_CANCELLATION_PRE_REVIEW.md` SHA-256 `6bd5adcd58819b4ad585bb25fd565ee33453c51c341e58e1ccf136a6cbfe9175` was independently approved. Frozen prerequisites: `RegularizedBaseCoeff.lean` SHA-256 `09aac1a792bbfaf481c94ff2ff2f294bb2ea451afe87d2b3aa9199b34cac4aa6` and `RegularizedBaseFactorFourier.lean` SHA-256 `2afdee09ed97dbae6b64529c8a0af23c322ce57619e6b658e3355f52872b64fc`; the latter has a passing pinned build and parent independent imported kernel audit, and its final review is being written.

## Exact public Lean surface

Define the **literal** bilateral Fourier weight and Wiener size, with `natAbs` only as an exact representation of integer absolute value:

```lean
noncomputable def wienerWeight (k : ℤ) : ℝ :=
  (1 + (k.natAbs : ℝ)) ^ (9 / 8 : ℝ)

noncomputable def weightedWienerSize (f : Circle → ℂ) : ℝ :=
  ∑' k : ℤ, wienerWeight k * ‖FourierCoefficient f k‖

theorem summable_regularizedBaseFactor_wiener :
  Summable (fun k : ℤ =>
    wienerWeight k * ‖FourierCoefficient regularizedBaseFactor k‖)

theorem regularizedBaseFactor_wiener_eq :
  weightedWienerSize regularizedBaseFactor =
    (2 : ℝ) ^ (9 / 8 : ℝ) +
      ∑' n : ℕ,
        ((n + 1 : ℝ) ^ (9 / 8 : ℝ)) * ‖regularizedBaseCoeff n‖
```

The second theorem states an actual equality of finite real `tsum`s, with the first theorem supplying summability; `weightedWienerSize` as a general totalized `tsum` has no finiteness assertion for arbitrary `f`. The exponent is the real number `9/8`, **not** integer division. The Fourier coefficients are the frozen normalized real-interval integrals, already identified in the exact reviewed `regularizedBaseFactor_fourier` theorem. No independent formal coefficient field is introduced.

## Mathematical and numerical review

The reviewed Fourier theorem gives `F_1=1`, `F_{-n}=d_n` for every `n≥0`, and `F_k=0` for every integer `k≥2`, where `F=(1+s)g_{0,∂}` and `d_n=c_n+c_{n+1}`. The positive side of the bilateral sum therefore contributes only `w(1)|F_1|=2^(9/8)`. The nonpositive side is indexed bijectively by `k=-n`, `n∈ℕ`, with weight `w(-n)=(n+1)^(9/8)` and contribution `(n+1)^(9/8)|d_n|`. There is exactly one zero-frequency term `n=0`; neither side counts it twice. The unconditional weighted summability of the `d_n` terms is the public `summable_regularizedBaseCoeff_weighted` theorem in the frozen coefficient module. The `+1` Fourier term is finite. Thus the bilateral weighted sum is summable and has exactly the displayed value. A proof can use Mathlib's `summable_int_iff_summable_nat_and_neg_add_one` and `tsum_of_add_one_of_neg_add_one` (or an equivalent disjoint integer partition), taking care to align the negative tail with `n+1`.

Exact endpoint checks: `F_1=1`, `w(1)=2^(9/8)`; `F_0=d_0=3/2`, `w(0)=1`; `F_{-1}=d_1=3/8`, `w(-1)=2^(9/8)`; `F_{-2}=d_2=-1/16`, `w(-2)=3^(9/8)`; `F_2=0`. These use rational Fourier values and literal real-power weights, with no floating approximation. The norm sum is strictly positive since its `k=1` term is positive. If needed later, a separate positivity theorem may be added after its own source review; it is not part of this gate.

This gate proves the weighted Wiener finiteness and exact value for the **actual** regularized exterior factor. The finite endpoint division `P₋=(1+s)Q₋`, convolution norm bound for `g₀P₋`, other four source smallness inequalities, background-dependent inverse estimates, and frozen negative Target remain open. Implement in one new unimported module only after independent mathematical review of this exact signature; freeze its source SHA and obtain separate source/signature/imported-kernel final audit before aggregate import.
