import NLA.Proofs.SP14.EndpointWeightedKernelSchur
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
Finite complex Schur estimate for the actual Fourier matrix of the endpoint
extension. Infinite-dimensional extension remains separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 4000000

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

/-- Sobolev-weighted actual Fourier entry, with negative mode `-(t+1)`. -/
noncomputable def endpointFiniteFourierEntry (r : ℝ) (t k : ℕ) : ℂ :=
  (((((t + 1 : ℕ) : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r))) : ℝ) : ℂ) *
    FourierCoefficient
      (fun z => endpointBaseSymbol z * endpointInverseMonomial k z)
      (-((t + 1 : ℕ) : ℤ))

theorem endpointFiniteFourierEntry_norm (r : ℝ) (t k : ℕ) :
    ‖endpointFiniteFourierEntry r t k‖ = endpointWeightedKernel r (t + 1) k := by
  have hfac : 0 ≤ (((t + 1 : ℕ) : ℝ) ^ r) *
      (((k + 1 : ℕ) : ℝ) ^ (-r)) := by positivity
  unfold endpointFiniteFourierEntry endpointWeightedKernel endpointKernelAbs
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfac]

private theorem finite_schur_cauchy {ι : Type*} (s : Finset ι)
    (M v : ι → ℝ) (x : ι → ℂ)
    (hM : ∀ i ∈ s, 0 ≤ M i) (hv : ∀ i ∈ s, 0 < v i) :
    (∑ i ∈ s, M i * ‖x i‖) ^ 2 ≤
      (∑ i ∈ s, M i * v i) *
        (∑ i ∈ s, M i * ‖x i‖ ^ 2 / v i) := by
  classical
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => M i * ‖x i‖)
    (f := fun i => M i * v i)
    (g := fun i => M i * ‖x i‖ ^ 2 / v i)
  · intro i hi
    exact mul_nonneg (hM i hi) (hv i hi).le
  · intro i hi
    exact div_nonneg (mul_nonneg (hM i hi) (sq_nonneg _)) (hv i hi).le
  · intro i hi
    have hvi := hv i hi
    field_simp
    exact le_refl _

private theorem finite_schur_row {ι κ : Type*} (s : Finset κ)
    (a : ι → κ → ℂ) (M : ι → κ → ℝ) (w : ι → ℝ) (v : κ → ℝ)
    (C : ℝ) (x : κ → ℂ) (i : ι)
    (hM : ∀ k ∈ s, 0 ≤ M i k)
    (hv : ∀ k ∈ s, 0 < v k)
    (ha : ∀ k ∈ s, ‖a i k‖ ≤ M i k)
    (hrow : (∑ k ∈ s, M i k * v k) ≤ C * w i) :
    ‖∑ k ∈ s, a i k * x k‖ ^ 2 ≤
      C * w i * (∑ k ∈ s, M i k * ‖x k‖ ^ 2 / v k) := by
  classical
  have htri : ‖∑ k ∈ s, a i k * x k‖ ≤ ∑ k ∈ s, M i k * ‖x k‖ := by
    calc
      _ ≤ ∑ k ∈ s, ‖a i k * x k‖ := norm_sum_le _ _
      _ = ∑ k ∈ s, ‖a i k‖ * ‖x k‖ := by simp_rw [norm_mul]
      _ ≤ ∑ k ∈ s, M i k * ‖x k‖ := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_right (ha k hk) (norm_nonneg _)
  have hsumpos : 0 ≤ ∑ k ∈ s, M i k * ‖x k‖ :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (hM k hk) (norm_nonneg _))
  have hSpos : 0 ≤ ∑ k ∈ s, M i k * ‖x k‖ ^ 2 / v k :=
    Finset.sum_nonneg (fun k hk =>
      div_nonneg (mul_nonneg (hM k hk) (sq_nonneg _)) (hv k hk).le)
  have hsq : ‖∑ k ∈ s, a i k * x k‖ ^ 2 ≤
      (∑ k ∈ s, M i k * ‖x k‖) ^ 2 := by
    nlinarith [norm_nonneg (∑ k ∈ s, a i k * x k)]
  calc
    _ ≤ (∑ k ∈ s, M i k * ‖x k‖) ^ 2 := hsq
    _ ≤ (∑ k ∈ s, M i k * v k) *
          (∑ k ∈ s, M i k * ‖x k‖ ^ 2 / v k) :=
      finite_schur_cauchy s (M i) v x hM hv
    _ ≤ C * w i * (∑ k ∈ s, M i k * ‖x k‖ ^ 2 / v k) :=
      mul_le_mul_of_nonneg_right hrow hSpos

private theorem finite_schur_matrix {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → κ → ℂ) (M : ι → κ → ℝ) (w : ι → ℝ) (v : κ → ℝ)
    (C : ℝ) (x : κ → ℂ) (hC : 0 ≤ C)
    (hM : ∀ i ∈ s, ∀ k ∈ t, 0 ≤ M i k)
    (hv : ∀ k ∈ t, 0 < v k)
    (ha : ∀ i ∈ s, ∀ k ∈ t, ‖a i k‖ ≤ M i k)
    (hrow : ∀ i ∈ s, (∑ k ∈ t, M i k * v k) ≤ C * w i)
    (hcol : ∀ k ∈ t, (∑ i ∈ s, M i k * w i) ≤ C * v k) :
    (∑ i ∈ s, ‖∑ k ∈ t, a i k * x k‖ ^ 2) ≤
      C ^ 2 * (∑ k ∈ t, ‖x k‖ ^ 2) := by
  classical
  calc
    _ ≤ ∑ i ∈ s, C * w i *
          (∑ k ∈ t, M i k * ‖x k‖ ^ 2 / v k) := by
      apply Finset.sum_le_sum
      intro i hi
      exact finite_schur_row t a M w v C x i (hM i hi) hv (ha i hi) (hrow i hi)
    _ = ∑ i ∈ s, ∑ k ∈ t,
          C * (‖x k‖ ^ 2 / v k) * (M i k * w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ k ∈ t, ∑ i ∈ s,
          C * (‖x k‖ ^ 2 / v k) * (M i k * w i) := Finset.sum_comm
    _ = ∑ k ∈ t, C * (‖x k‖ ^ 2 / v k) *
          (∑ i ∈ s, M i k * w i) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ t, C * (‖x k‖ ^ 2 / v k) * (C * v k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hcol k hk)
        (mul_nonneg hC (div_nonneg (sq_nonneg _) (hv k hk).le))
    _ = C ^ 2 * (∑ k ∈ t, ‖x k‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hvk := hv k hk
      field_simp

private theorem endpointFiniteFourier_row (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (J N : ℕ) (t : Fin J) :
    (∑ k : Fin N, endpointWeightedKernel r (t.val + 1) k.val *
      (1 / Real.sqrt (((k.val + 1 : ℕ) : ℝ)))) ≤
        endpointSchurConstant r * (1 / Real.sqrt (((t.val + 1 : ℕ) : ℝ))) := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ k ∈ Finset.range N,
        endpointWeightedKernel r (t.val + 1) k *
          (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [Finset.mem_range.mp hk]
    _ ≤ _ := endpointWeightedKernel_row_sum_le r hr hr1 (t.val + 1) N (by omega)

private theorem endpointFiniteFourier_column (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (J N : ℕ) (k : Fin N) :
    (∑ t : Fin J, endpointWeightedKernel r (t.val + 1) k.val *
      (1 / Real.sqrt (((t.val + 1 : ℕ) : ℝ)))) ≤
        endpointSchurConstant r * (1 / Real.sqrt (((k.val + 1 : ℕ) : ℝ))) := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ t ∈ Finset.range J,
        endpointWeightedKernel r (t + 1) k.val *
          (1 / Real.sqrt (((t + 1 : ℕ) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp [Finset.mem_range.mp ht]
    _ ≤ _ := endpointWeightedKernel_column_sum_le r hr hr1 k.val J

/-- Finite complex Schur bound for the actual negative Fourier matrix. -/
theorem endpointFiniteFourierMatrix_bound (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (J N : ℕ) (x : Fin N → ℂ) :
    (∑ t : Fin J,
      ‖∑ k : Fin N, endpointFiniteFourierEntry r t.val k.val * x k‖ ^ 2) ≤
      endpointSchurConstant r ^ 2 * (∑ k : Fin N, ‖x k‖ ^ 2) := by
  classical
  let M : Fin J → Fin N → ℝ := fun t k => endpointWeightedKernel r (t.val + 1) k.val
  let w : Fin J → ℝ := fun t => 1 / Real.sqrt (((t.val + 1 : ℕ) : ℝ))
  let v : Fin N → ℝ := fun k => 1 / Real.sqrt (((k.val + 1 : ℕ) : ℝ))
  have hC : 0 ≤ endpointSchurConstant r := by
    unfold endpointSchurConstant
    have : 0 < 1 - r := by linarith
    positivity
  have hM : ∀ t ∈ (Finset.univ : Finset (Fin J)),
      ∀ k ∈ (Finset.univ : Finset (Fin N)), 0 ≤ M t k := by
    intro t ht k hk
    dsimp [M, endpointWeightedKernel, endpointKernelAbs]
    positivity
  have hv : ∀ k ∈ (Finset.univ : Finset (Fin N)), 0 < v k := by
    intro k hk
    dsimp [v]
    positivity
  have ha : ∀ t ∈ (Finset.univ : Finset (Fin J)),
      ∀ k ∈ (Finset.univ : Finset (Fin N)),
      ‖endpointFiniteFourierEntry r t.val k.val‖ ≤ M t k := by
    intro t ht k hk
    exact (endpointFiniteFourierEntry_norm r t.val k.val).le
  have hrow : ∀ t ∈ (Finset.univ : Finset (Fin J)),
      (∑ k : Fin N, M t k * v k) ≤ endpointSchurConstant r * w t := by
    intro t ht
    exact endpointFiniteFourier_row r hr hr1 J N t
  have hcol : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      (∑ t : Fin J, M t k * w t) ≤ endpointSchurConstant r * v k := by
    intro k hk
    exact endpointFiniteFourier_column r hr hr1 J N k
  have hbound := finite_schur_matrix
    (s := (Finset.univ : Finset (Fin J)))
    (t := (Finset.univ : Finset (Fin N)))
    (a := fun t k => endpointFiniteFourierEntry r t.val k.val)
    (M := M) (w := w) (v := v) (C := endpointSchurConstant r)
    (x := x) hC hM hv ha hrow hcol
  exact hbound

#assert_trust kernel endpointFiniteFourierEntry_norm
#print axioms endpointFiniteFourierEntry_norm
#assert_trust kernel endpointFiniteFourierMatrix_bound
#print axioms endpointFiniteFourierMatrix_bound

end NLA.Proofs.SP14
