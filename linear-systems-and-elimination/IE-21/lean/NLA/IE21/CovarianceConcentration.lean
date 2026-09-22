import NLA.IE21.Chernoff
import NLA.IE21.QuadraticNet

/-! Exact covariance tail from the actual spherical-row MGF.
Original analytic argument: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NLA.IE21

lemma directional_quadratic_tail_of_mgf (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1)
    (hmgf : ∀ a : ℝ, |a| ≤ 1 / 8 →
      Integrable (fun u => Real.exp (a * (directionalEnergy x u - 1))) (sphereLaw n) ∧
      (∫ u, Real.exp (a * (directionalEnergy x u - 1)) ∂sphereLaw n) ≤
        Real.exp (32 * a ^ 2))
    (s : ℝ) (hs : 0 < s ∧ s ≤ 1) :
    (matrixLaw m n).real {A | s < |inner ℝ (covarianceOperator A x) x|} ≤
      2 * Real.exp (-(m : ℝ) * s ^ 2 / 128) := by
  have hp := product_row_semantics m n hn
  let : IsProbabilityMeasure (matrixLaw m n) := hp.1
  let X : Fin m → Mat m n → ℝ := fun i A => directionalEnergy x (matrixRow A i) - 1
  have hX : ∀ i, Measurable (X i) := by intro i; unfold X directionalEnergy matrixRow; fun_prop
  have hind : iIndepFun X (matrixLaw m n) :=
    hp.2.1.2.1.comp (fun _ u => directionalEnergy x u - 1) (by intro i; unfold directionalEnergy; fun_prop)
  have hmom : ∀ a : ℝ, |a| ≤ 1 / 8 → ∀ i,
      Integrable (fun A => Real.exp (a * X i A)) (matrixLaw m n) ∧
      mgf (X i) (matrixLaw m n) a ≤ Real.exp (32 * a ^ 2) := by
    intro a ha i
    have hrow := hp.2.1.2.2 i
    have hmrow := measurable_matrixRow m n i
    let f : Space n → ℝ := fun u => Real.exp (a * (directionalEnergy x u - 1))
    have hf : Measurable f := by unfold f directionalEnergy; fun_prop
    have hi : Integrable f ((matrixLaw m n).map (fun A => matrixRow A i)) := by
      rw [hrow]
      exact (hmgf a ha).1
    refine ⟨?_, ?_⟩
    · exact (integrable_map_measure hf.aestronglyMeasurable hmrow.aemeasurable).mp hi
    · have heq : (∫ u, f u ∂sphereLaw n) = ∫ A, f (matrixRow A i) ∂matrixLaw m n := by
        rw [← hrow, integral_map hmrow.aemeasurable hf.aestronglyMeasurable]
      change (∫ A, f (matrixRow A i) ∂matrixLaw m n) ≤ _
      rw [← heq]
      exact (hmgf a ha).2
  have h := independent_mgf_average_tail (matrixLaw m n) hm X hX hind hmom s hs
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have heq (A : Mat m n) : (∑ i, X i A) / (m : ℝ) =
      inner ℝ (covarianceOperator A x) x := by
    rw [covariance_quadratic_rows A x hx]
    simp only [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  simpa only [heq] using h

lemma covariance_concentration_of_mgf (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (hmgf : ∀ (x : Space n), ‖x‖ = 1 → ∀ a : ℝ, |a| ≤ 1 / 8 →
      Integrable (fun u => Real.exp (a * (directionalEnergy x u - 1))) (sphereLaw n) ∧
      (∫ u, Real.exp (a * (directionalEnergy x u - 1)) ∂sphereLaw n) ≤
        Real.exp (32 * a ^ 2))
    (t : ℝ) (ht : 0 < t ∧ t ≤ 1) :
    (matrixLaw m n).real {A | covarianceError A > t} ≤
      2 * (9 : ℝ) ^ n * Real.exp (-(m : ℝ) * t ^ 2 / 512) := by
  classical
  have hn1 : 1 ≤ n := by omega
  let : IsProbabilityMeasure (matrixLaw m n) := (product_row_semantics m n hn1).1
  obtain ⟨C, hC, hcard, hcover⟩ := sphere_net n hn1 (1 / 4) (by norm_num)
  norm_num at hcard
  let E : Space n → Set (Mat m n) := fun x => {A | t / 2 < |inner ℝ (covarianceOperator A x) x|}
  have hsub : {A : Mat m n | covarianceError A > t} ⊆ ⋃ x ∈ C, E x := by
    intro A hA
    obtain ⟨x, hx, hb⟩ := covariance_net_witness A C hC hcover t ht.1.le hA
    exact mem_iUnion₂.mpr ⟨x, hx, hb⟩
  have htail (x : Space n) (hx : x ∈ C) :
      (matrixLaw m n).real (E x) ≤ 2 * Real.exp (-(m : ℝ) * t ^ 2 / 512) := by
    have h := directional_quadratic_tail_of_mgf m n hm hn1 x (hC x hx)
      (hmgf x (hC x hx)) (t / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have he : -(m : ℝ) * (t / 2) ^ 2 / 128 = -(m : ℝ) * t ^ 2 / 512 := by ring
    simpa only [E, he] using h
  calc
    _ ≤ (matrixLaw m n).real (⋃ x ∈ C, E x) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ x ∈ C, (matrixLaw m n).real (E x) := measureReal_biUnion_finset_le C E
    _ ≤ ∑ _x ∈ C, 2 * Real.exp (-(m : ℝ) * t ^ 2 / 512) :=
      Finset.sum_le_sum htail
    _ = (C.card : ℝ) * (2 * Real.exp (-(m : ℝ) * t ^ 2 / 512)) := by simp
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hcard
        (show 0 ≤ 2 * Real.exp (-(m : ℝ) * t ^ 2 / 512) by positivity)
      nlinarith [hh]

end NLA.IE21
