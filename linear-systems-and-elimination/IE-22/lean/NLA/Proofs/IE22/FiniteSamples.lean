import Mathlib
import NLA.Statements.IE22

/-! Finite simultaneous approximation of bounded expectations by actual samples.
The sample law is the genuine finite product measure; no independence between
separate tests on one outcome is required. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators ENNReal
open Set MeasureTheory ProbabilityTheory
namespace NLA.Proofs.IE22

/-- Every finite family of bounded measurable real tests admits an arbitrarily
large finite actual sample approximating all its expectations strictly. -/
theorem exists_finite_sample {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : J → Ω → ℝ) (T : ℝ) (_hT : 0 ≤ T)
    (hf : ∀ j, AEStronglyMeasurable (f j) μ)
    (hbound : ∀ j x, 0 ≤ f j x ∧ f j x ≤ T)
    (ε : ℝ) (hε : 0 < ε) (M0 : ℕ) :
    ∃ m : ℕ, 0 < m ∧ M0 ≤ m ∧ ∃ ω : Fin m → Ω,
      ∀ j, |(1 / (m : ℝ)) * (∑ i, f j (ω i)) - ∫ x, f j x ∂μ| < ε := by
  classical
  let C : ℝ := (Fintype.card J : ℝ) * T ^ 2 / ε ^ 2
  obtain ⟨m, hm⟩ := exists_nat_gt (max (M0 : ℝ) (max 0 C))
  have hm0R : (0 : ℝ) < m := lt_of_le_of_lt (le_trans (le_max_left 0 C)
    (le_max_right (M0 : ℝ) (max 0 C))) hm
  have hm0 : 0 < m := by exact_mod_cast hm0R
  have hmM : M0 ≤ m := by
    have h : (M0 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
    exact le_of_lt (by exact_mod_cast h)
  have hmC : C < m := lt_of_le_of_lt (le_trans (le_max_right 0 C)
    (le_max_right (M0 : ℝ) (max 0 C))) hm
  let P : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => μ)
  let avg : J → (Fin m → Ω) → ℝ := fun j ω => (1 / (m : ℝ)) * ∑ i, f j (ω i)
  have hfLp (j : J) : MemLp (f j) 2 μ :=
    memLp_of_bounded (Filter.Eventually.of_forall (hbound j)) (hf j) 2
  have hcoord (j : J) (i : Fin m) : MemLp (fun ω : Fin m → Ω => f j (ω i)) 2 P :=
    (hfLp j).comp_measurePreserving (measurePreserving_eval _ i)
  have havgLp (j : J) : MemLp (avg j) 2 P := by
    exact (memLp_finsetSum _ (fun i _ => hcoord j i)).const_mul _
  have havgInt (j : J) : ∫ ω, avg j ω ∂P = ∫ x, f j x ∂μ := by
    have heval (i : Fin m) : ∫ ω, f j (ω i) ∂P = ∫ x, f j x ∂μ :=
      integral_comp_eval (μ := fun _ : Fin m => μ) (i := i) (hf j)
    dsimp [avg]
    rw [integral_const_mul, integral_finsetSum]
    · simp_rw [heval]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · exact fun i _ => (hcoord j i).integrable (by norm_num)
  have hvar (j : J) : variance (avg j) P ≤ T ^ 2 / (m : ℝ) := by
    have hv : variance (f j) μ ≤ T ^ 2 := by
      have h := variance_le_sq_of_bounded (Filter.Eventually.of_forall (hbound j))
        (hf j).aemeasurable
      nlinarith [sq_nonneg T]
    have heq : variance (avg j) P = variance (f j) μ / (m : ℝ) := by
      dsimp [avg]
      rw [variance_const_mul]
      have hs : variance (fun ω : Fin m → Ω => ∑ i, f j (ω i)) P =
          (m : ℝ) * variance (f j) μ := by
        have hh := variance_sum_pi (μ := fun _ : Fin m => μ)
          (X := fun _ => f j) (fun _ => hfLp j)
        have hfun : (fun ω : Fin m → Ω => ∑ i, f j (ω i)) =
            ∑ i : Fin m, fun ω => f j (ω i) := by ext ω; simp
        rw [hfun]
        simpa only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul] using hh
      rw [hs]
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right hv hm0R.le
  let bad : J → Set (Fin m → Ω) := fun j => {ω | ε ≤ |avg j ω - ∫ x, f j x ∂μ|}
  have hbad (j : J) : P (bad j) ≤ ENNReal.ofReal (T ^ 2 / ((m : ℝ) * ε ^ 2)) := by
    have h := meas_ge_le_variance_div_sq (havgLp j) hε
    rw [havgInt j] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      variance (avg j) P / ε ^ 2 ≤ (T ^ 2 / (m : ℝ)) / ε ^ 2 :=
        div_le_div_of_nonneg_right (hvar j) (sq_nonneg ε)
      _ = T ^ 2 / ((m : ℝ) * ε ^ 2) := by ring
  have hnonneg : 0 ≤ T ^ 2 / ((m : ℝ) * ε ^ 2) :=
    div_nonneg (sq_nonneg T) (mul_nonneg hm0R.le (sq_nonneg ε))
  have hunion : P (⋃ j, bad j) < 1 := by
    calc
      P (⋃ j, bad j) ≤ ∑ j, P (bad j) := measure_iUnion_fintype_le P bad
      _ ≤ ∑ _j : J, ENNReal.ofReal (T ^ 2 / ((m : ℝ) * ε ^ 2)) :=
        Finset.sum_le_sum (fun j _ => hbad j)
      _ = ENNReal.ofReal ((Fintype.card J : ℝ) * (T ^ 2 / ((m : ℝ) * ε ^ 2))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hnonneg)]
        simp
      _ < 1 := by
        apply ENNReal.ofReal_lt_one.mpr
        have hquot : C / (m : ℝ) < 1 := (div_lt_one hm0R).mpr hmC
        have halg : (Fintype.card J : ℝ) * (T ^ 2 / ((m : ℝ) * ε ^ 2)) =
            C / (m : ℝ) := by dsimp [C]; ring
        rw [halg]
        exact hquot
  have hne : (⋃ j, bad j) ≠ univ := by
    intro heq
    rw [heq, measure_univ] at hunion
    exact (lt_irrefl _ hunion)
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨m, hm0, hmM, ω, fun j => ?_⟩
  have hj : ω ∉ bad j := fun hj => hω (mem_iUnion.mpr ⟨j, hj⟩)
  exact lt_of_not_ge hj

#assert_trust kernel exists_finite_sample
#print axioms exists_finite_sample
end NLA.Proofs.IE22
