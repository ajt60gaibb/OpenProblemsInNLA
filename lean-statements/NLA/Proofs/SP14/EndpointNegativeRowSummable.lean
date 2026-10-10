import NLA.Proofs.SP14.EndpointNegativeRow
import NLA.Proofs.SP14.WeightedSobolevPhysical

/-!
Absolute summability of the actual negative Fourier row paired with any
weighted Sobolev coefficient vector. The row square bound is unconditional.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- Every actual negative Fourier row is square summable. -/
theorem summable_endpointFiniteFourierRow_norm_sq (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (t : ℕ) :
    Summable (fun k : ℕ => ‖endpointFiniteFourierEntry r t k‖ ^ 2) := by
  apply summable_of_sum_range_le (fun k => sq_nonneg _)
  intro N
  calc
    (∑ k ∈ Finset.range N, ‖endpointFiniteFourierEntry r t k‖ ^ 2) =
        ∑ k : Fin N, ‖endpointFiniteFourierEntry r t k.val‖ ^ 2 := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      simp [Finset.mem_range.mp hk]
    _ ≤ endpointSchurConstant r ^ 2 :=
      endpointFiniteFourierRow_square_sum_le r hr hr1 t N

/-- The row as an element of the same complete complex `lp 2` carrier. -/
noncomputable def endpointNegativeRowLp (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (t : ℕ) : SobolevCoeff r :=
  ⟨fun k : ℕ => endpointFiniteFourierEntry r t k, by
    apply memℓp_gen
    simpa using summable_endpointFiniteFourierRow_norm_sq r hr hr1 t⟩

theorem endpointNegativeRowLp_apply (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (t k : ℕ) :
    endpointNegativeRowLp r hr hr1 t k = endpointFiniteFourierEntry r t k := rfl

/-- The actual Fourier product series is absolutely summable for every input. -/
theorem summable_endpointFiniteFourierEntry_mul
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (t : ℕ) :
    Summable (fun k : ℕ => endpointFiniteFourierEntry r t k * y k) := by
  have h22 : (ENNReal.toReal (2 : ENNReal)).HolderConjugate
      (ENNReal.toReal (2 : ENNReal)) := by
    change (2 : ℝ).HolderConjugate 2
    constructor <;> norm_num
  have hprod := lp.summable_mul h22 (endpointNegativeRowLp r hr hr1 t) y
  apply Summable.of_norm
  simpa [endpointNegativeRowLp_apply, norm_mul] using hprod

#assert_trust kernel summable_endpointFiniteFourierRow_norm_sq
#assert_trust kernel summable_endpointFiniteFourierEntry_mul
#print axioms summable_endpointFiniteFourierEntry_mul

end NLA.Proofs.SP14
