import NLA.Proofs.SP14.EndpointInverseL2Dense

/-!
The actual finite triangular inverse as a bounded complex-linear map on
finite-support weighted inputs. The full probability-Haar `L²` extension is a
subsequent gate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 400000

namespace NLA.Proofs.SP14

local instance finiteSupportTwoPiPositive : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

private theorem endpointFiniteSupport_eq_truncation (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → y n = 0) :
    sobolevTruncation r N y = y := by
  ext n
  rw [sobolevTruncation_apply]
  by_cases hn : n < N
  · simp [hn]
  · simp [hn, hN n (by omega)]

/-- The literal first-`N` weighted truncation viewed in the exact dense
finite-support submodule. -/
noncomputable def endpointFiniteSupportTruncation (r : ℝ)
    (N : ℕ) (y : SobolevCoeff r) : endpointFiniteSupport r :=
  ⟨sobolevTruncation r N y, by
    refine ⟨N, ?_⟩
    intro n hn
    rw [sobolevTruncation_apply]
    simp [not_lt.mpr hn]⟩

private theorem endpointFiniteInverseLp_eq_of_support (r : ℝ)
    (y : SobolevCoeff r) (M N : ℕ)
    (hM : ∀ n : ℕ, M ≤ n → y n = 0)
    (hN : ∀ n : ℕ, N ≤ n → y n = 0) :
    endpointFiniteInverseLp r y M = endpointFiniteInverseLp r y N := by
  let K := max M N
  have hMK : M ≤ K := le_max_left M N
  have hNK : N ≤ K := le_max_right M N
  calc
    endpointFiniteInverseLp r y M =
        endpointFiniteInverseLp r (sobolevTruncation r M y) K :=
      (endpointFiniteInverseLp_truncation r y M K hMK).symm
    _ = endpointFiniteInverseLp r y K := by
      rw [endpointFiniteSupport_eq_truncation r y M hM]
    _ = endpointFiniteInverseLp r (sobolevTruncation r N y) K := by
      rw [endpointFiniteSupport_eq_truncation r y N hN]
    _ = endpointFiniteInverseLp r y N :=
      endpointFiniteInverseLp_truncation r y N K hNK

private noncomputable def endpointFiniteSupportInverseVal (r : ℝ)
    (y : endpointFiniteSupport r) :
    MeasureTheory.Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)) :=
  endpointFiniteInverseLp r y (Classical.choose y.property)

private theorem endpointFiniteSupportInverseVal_eq (r : ℝ)
    (y : endpointFiniteSupport r) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → (y : SobolevCoeff r) n = 0) :
    endpointFiniteSupportInverseVal r y = endpointFiniteInverseLp r y N := by
  exact endpointFiniteInverseLp_eq_of_support r y _ N
    (Classical.choose_spec y.property) hN

/-- The finite triangular inverse is a complex-linear map on the exact dense
finite-support submodule. The chosen support bound does not affect its value. -/
noncomputable def endpointFiniteSupportInverse (r : ℝ) :
    endpointFiniteSupport r →ₗ[ℂ]
      MeasureTheory.Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)) where
  toFun := endpointFiniteSupportInverseVal r
  map_add' := by
    intro y z
    let M := Classical.choose y.property
    let N := Classical.choose z.property
    let K := max M N
    have hM : ∀ n : ℕ, M ≤ n → (y : SobolevCoeff r) n = 0 :=
      Classical.choose_spec y.property
    have hN : ∀ n : ℕ, N ≤ n → (z : SobolevCoeff r) n = 0 :=
      Classical.choose_spec z.property
    have hKy : ∀ n : ℕ, K ≤ n → (y : SobolevCoeff r) n = 0 := by
      intro n hn
      exact hM n (le_trans (le_max_left M N) hn)
    have hKz : ∀ n : ℕ, K ≤ n → (z : SobolevCoeff r) n = 0 := by
      intro n hn
      exact hN n (le_trans (le_max_right M N) hn)
    have hKsum : ∀ n : ℕ, K ≤ n → ((y + z : endpointFiniteSupport r) : SobolevCoeff r) n = 0 := by
      intro n hn
      simp [hKy n hn, hKz n hn]
    change endpointFiniteSupportInverseVal r (y + z) =
      endpointFiniteSupportInverseVal r y + endpointFiniteSupportInverseVal r z
    calc
      endpointFiniteSupportInverseVal r (y + z) =
          endpointFiniteInverseLp r (y + z) K :=
        endpointFiniteSupportInverseVal_eq r (y + z) K hKsum
      _ = endpointFiniteInverseLp r y K + endpointFiniteInverseLp r z K :=
        endpointFiniteInverseLp_add r y z K
      _ = endpointFiniteSupportInverseVal r y +
          endpointFiniteSupportInverseVal r z := by
        rw [endpointFiniteSupportInverseVal_eq r y K hKy,
          endpointFiniteSupportInverseVal_eq r z K hKz]
  map_smul' := by
    intro c y
    let N := Classical.choose y.property
    have hN : ∀ n : ℕ, N ≤ n → (y : SobolevCoeff r) n = 0 :=
      Classical.choose_spec y.property
    have hNc : ∀ n : ℕ, N ≤ n → ((c • y : endpointFiniteSupport r) : SobolevCoeff r) n = 0 := by
      intro n hn
      simp [hN n hn]
    change endpointFiniteSupportInverseVal r (c • y) =
      c • endpointFiniteSupportInverseVal r y
    calc
      endpointFiniteSupportInverseVal r (c • y) =
          endpointFiniteInverseLp r (c • y) N :=
        endpointFiniteSupportInverseVal_eq r (c • y) N hNc
      _ = c • endpointFiniteInverseLp r y N :=
        endpointFiniteInverseLp_smul r c y N
      _ = c • endpointFiniteSupportInverseVal r y := by
        rw [endpointFiniteSupportInverseVal_eq r y N hN]

/-- A finite-support inverse equals the exact finite inverse at every valid
support bound, including the empty bound. -/
theorem endpointFiniteSupportInverse_eq_finite (r : ℝ)
    (y : endpointFiniteSupport r) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → (y : SobolevCoeff r) n = 0) :
    endpointFiniteSupportInverse r y = endpointFiniteInverseLp r y N :=
  endpointFiniteSupportInverseVal_eq r y N hN

/-- The pre-reviewed Hilbert–Schmidt constant bounds the actual map on the
dense finite-support domain. -/
theorem endpointFiniteSupportInverse_norm_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : endpointFiniteSupport r) :
    ‖endpointFiniteSupportInverse r y‖ ≤
      endpointInverseHSBound r * ‖y‖ := by
  let N := Classical.choose y.property
  rw [endpointFiniteSupportInverse_eq_finite r y N (Classical.choose_spec y.property)]
  exact endpointFiniteInverseLp_norm_le r hrHalf y N

/-- The finite-support map evaluates on the literal truncation to the source's
finite inverse polynomial in probability-Haar `L²`. -/
theorem endpointFiniteSupportInverse_truncation (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    endpointFiniteSupportInverse r (endpointFiniteSupportTruncation r N y) =
      endpointFiniteInverseLp r y N := by
  rw [endpointFiniteSupportInverse_eq_finite r
    (endpointFiniteSupportTruncation r N y) N]
  · change endpointFiniteInverseLp r (sobolevTruncation r N y) N =
      endpointFiniteInverseLp r y N
    exact endpointFiniteInverseLp_truncation r y N N le_rfl
  · intro n hn
    change sobolevTruncation r N y n = 0
    rw [sobolevTruncation_apply]
    simp [not_lt.mpr hn]

#assert_trust kernel endpointFiniteSupportInverse_eq_finite
#assert_trust kernel endpointFiniteSupportInverse_norm_le
#assert_trust kernel endpointFiniteSupportInverse_truncation
#print axioms endpointFiniteSupportInverse_truncation

end NLA.Proofs.SP14
