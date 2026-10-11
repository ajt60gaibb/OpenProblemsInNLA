# SP-14 endpoint realization difference: independent pre-implementation review

**Disposition:** approve the two exact helper signatures below under the already reviewed endpoint-vanishing contract. They are necessary to pass finite-input vanishing to arbitrary input; neither proves the frozen negative Target.

I independently checked the proposal from `/root/sp14_base_proof` against `ENDPOINT_VANISHING_BY_DENSITY_PRE_REVIEW.md` at SHA-256 `4f8d9e612f7781473cc781c096113c8f11121409feb235b7e841019e523c88d2`, the unchanged frozen SP-14 statement, and the actual `EndpointCircleSeries.lean` at SHA-256 `a3ea7def39f80cb3b898a0b68c81146d51cf96541f2e1ca8c05e701764288162` and `EndpointNegativeOperator.lean` at SHA-256 `16685a4f52b47911d79fc79b78cbdd9117e3efcb914e5102e0b068da118442b1` definitions. The proposed exact Lean signatures are:

```lean
theorem endpointCircleRealization_sub
    (r : ℝ) (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y x : SobolevCoeff r) (z : Circle) :
    endpointCircleRealization r hrHalf hr1 (y - x) z =
      endpointCircleRealization r hrHalf hr1 y z -
        endpointCircleRealization r hrHalf hr1 x z

theorem endpointCircleRealization_pointwise_sub_norm_le
    (r : ℝ) (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y x : SobolevCoeff r) (z : Circle) :
    ‖endpointCircleRealization r hrHalf hr1 y z -
        endpointCircleRealization r hrHalf hr1 x z‖ ≤
      ‖endpointCircleWeightLp r hrHalf‖ *
        (1 + endpointSchurConstant r) * ‖y - x‖
```

The first follows because `physicalCoeff r` is coordinatewise complex-linear, `endpointNegativeOperator` is the actual bounded complex-linear map, and both mode series are absolutely summable, so `tsum_sub` applies separately to the positive and strictly negative Fourier modes. It must be proved for every pair `y,x`, every `z`, including zero inputs, without an assumed finite support. The second is the previously approved pointwise norm bound applied to `y−x` after the first equality, so it keeps exactly the same coefficient `‖endpointCircleWeightLp r hrHalf‖(1+endpointSchurConstant r)` and **the actual weighted norm** `‖y−x‖`. No input continuity may be inferred from continuity only in `z`. These two statements need their own direct pinned Lean 4.33.1/LeanCert `kernel` check and separate imported exact-signature/source/axiom audit before aggregate import.
