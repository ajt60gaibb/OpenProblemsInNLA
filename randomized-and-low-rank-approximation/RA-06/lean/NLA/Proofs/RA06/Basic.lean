import NLA.Statements.RA06
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Initial kernel-checked reductions for the exact RA-06 target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA06

open NLA.Statements.RA06

/-- Every summand in the exact input energy is nonnegative. -/
theorem rowEnergy_nonneg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (i : Fin n) (x : Fin d → ℝ) :
    0 ≤ Real.rpow |RowValue A i x| p :=
  Real.rpow_nonneg (abs_nonneg _) _

/-- Full column rank makes the denominator in every ordinary sensitivity ratio positive. -/
theorem inputEnergy_pos {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (hA : FullColumnRank A) (x : Fin d → ℝ)
    (hx : ∃ j, x j ≠ 0) : 0 < InputEnergy A p x := by
  have hsome : ∃ i : Fin n, RowValue A i x ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := hx
    exact hj (hA x h j)
  obtain ⟨i, hi⟩ := hsome
  unfold InputEnergy
  apply Finset.sum_pos'
  · intro i _
    exact rowEnergy_nonneg A p i x
  · exact ⟨i, Finset.mem_univ _, Real.rpow_pos_of_pos (abs_pos.mpr hi) p⟩

/-- An ordinary row contribution is bounded by the full input energy. -/
theorem rowEnergy_le_inputEnergy {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p : ℝ)
    (i : Fin n) (x : Fin d → ℝ) :
    Real.rpow |RowValue A i x| p ≤ InputEnergy A p x := by
  unfold InputEnergy
  exact Finset.single_le_sum (fun j _ => rowEnergy_nonneg A p j x) (Finset.mem_univ i)

/-- Every ordinary sensitivity ratio lies in `[0,1]` for admissible inputs. -/
theorem sensitivityRatio_mem_unit {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p : ℝ)
    (hA : FullColumnRank A) (i : Fin n) (x : Fin d → ℝ)
    (hx : ∃ j, x j ≠ 0) :
    0 ≤ Real.rpow |RowValue A i x| p / InputEnergy A p x ∧
      Real.rpow |RowValue A i x| p / InputEnergy A p x ≤ 1 := by
  have hden := inputEnergy_pos A p hA x hx
  constructor
  · exact div_nonneg (rowEnergy_nonneg A p i x) hden.le
  · exact (div_le_one hden).mpr (rowEnergy_le_inputEnergy A p i x)

private theorem exists_nonzero_vector {d : ℕ} (hd : 0 < d) :
    ∃ x : Fin d → ℝ, ∃ j : Fin d, x j ≠ 0 := by
  let j : Fin d := ⟨0, hd⟩
  let x : Fin d → ℝ := fun k => if k = j then 1 else 0
  exact ⟨x, j, by simp [x]⟩

/-- Exact ordinary sensitivities are at most one. -/
theorem sensitivity_le_one {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p : ℝ)
    (hA : FullColumnRank A) (hd : 0 < d) (i : Fin n) :
    Sensitivity A p i ≤ 1 := by
  unfold Sensitivity
  apply csSup_le
  · obtain ⟨x, hx⟩ := exists_nonzero_vector hd
    exact ⟨_, x, hx, rfl⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (sensitivityRatio_mem_unit A p hA i x hx).2

/-- A uniform row-energy estimate bounds the actual supremum defining
ordinary sensitivity. -/
theorem sensitivity_le_of_rowEnergy_bound {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p K : ℝ)
    (hA : FullColumnRank A) (hd : 0 < d) (i : Fin n)
    (hrow : ∀ x : Fin d → ℝ,
      Real.rpow |RowValue A i x| p ≤ K * InputEnergy A p x) :
    Sensitivity A p i ≤ K := by
  unfold Sensitivity
  apply csSup_le
  · obtain ⟨x, hx⟩ := exists_nonzero_vector hd
    exact ⟨_, x, hx, rfl⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (div_le_iff₀ (inputEnergy_pos A p hA x hx)).mpr (hrow x)

/-- Exact ordinary sensitivities are nonnegative. -/
theorem sensitivity_nonneg {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p : ℝ)
    (hA : FullColumnRank A) (hd : 0 < d) (i : Fin n) :
    0 ≤ Sensitivity A p i := by
  obtain ⟨x, hx⟩ := exists_nonzero_vector hd
  have hbd : BddAbove {y : ℝ | ∃ x : Fin d → ℝ,
      (∃ j, x j ≠ 0) ∧
      y = Real.rpow |RowValue A i x| p / InputEnergy A p x} := by
    refine ⟨1, ?_⟩
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact (sensitivityRatio_mem_unit A p hA i z hz).2
  have hmem : Real.rpow |RowValue A i x| p / InputEnergy A p x ∈
      {y : ℝ | ∃ z : Fin d → ℝ,
        (∃ j, z j ≠ 0) ∧
        y = Real.rpow |RowValue A i z| p / InputEnergy A p z} := by
    exact ⟨x, hx, rfl⟩
  exact (sensitivityRatio_mem_unit A p hA i x hx).1.trans
    (by simpa only [Sensitivity] using le_csSup hbd hmem)

/-- Every admissible ordinary row ratio is bounded by the actual supremum. -/
theorem sensitivityRatio_le_sensitivity {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p : ℝ)
    (hA : FullColumnRank A) (i : Fin n) (x : Fin d → ℝ)
    (hx : ∃ j, x j ≠ 0) :
    Real.rpow |RowValue A i x| p / InputEnergy A p x ≤
      Sensitivity A p i := by
  have hbd : BddAbove {y : ℝ | ∃ z : Fin d → ℝ,
      (∃ j, z j ≠ 0) ∧
      y = Real.rpow |RowValue A i z| p / InputEnergy A p z} := by
    refine ⟨1, ?_⟩
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact (sensitivityRatio_mem_unit A p hA i z hz).2
  have hmem : Real.rpow |RowValue A i x| p / InputEnergy A p x ∈
      {y : ℝ | ∃ z : Fin d → ℝ,
        (∃ j, z j ≠ 0) ∧
        y = Real.rpow |RowValue A i z| p / InputEnergy A p z} :=
    ⟨x, hx, rfl⟩
  simpa only [Sensitivity] using le_csSup hbd hmem

/-- The floor and cap in RA-06 define a strictly positive probability. -/
theorem retentionProbability_pos {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α : ℝ)
    (hA : FullColumnRank A) (hn : 0 < n) (hd : 0 < d)
    (hα : 0 < α) (i : Fin n) :
    0 < RetentionProbability A p α i := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hscore : 0 ≤ Sensitivity A p i / α :=
    div_nonneg (sensitivity_nonneg A p hA hd i) hα.le
  unfold RetentionProbability
  exact lt_min (by norm_num) (add_pos_of_pos_of_nonneg (one_div_pos.mpr hnR) hscore)

/-- The saturated retention probability never exceeds one. -/
theorem retentionProbability_le_one {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α : ℝ) (i : Fin n) :
    RetentionProbability A p α i ≤ 1 := by
  unfold RetentionProbability
  exact min_le_left _ _

/-- The finite Bernoulli product gives every outcome nonnegative mass. -/
theorem outcomeWeight_nonneg {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α : ℝ)
    (hA : FullColumnRank A) (hn : 0 < n) (hd : 0 < d)
    (hα : 0 < α) (kept : Fin n → Bool) :
    0 ≤ OutcomeWeight A p α kept := by
  classical
  unfold OutcomeWeight
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact (retentionProbability_pos A p α hA hn hd hα i).le
  · exact sub_nonneg.mpr (retentionProbability_le_one A p α i)

/-- The product Bernoulli law in the exact target has total mass one. -/
theorem sum_outcomeWeight_eq_one {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α : ℝ) :
    (∑ kept : Fin n → Bool, OutcomeWeight A p α kept) = 1 := by
  classical
  calc
    (∑ kept : Fin n → Bool, OutcomeWeight A p α kept) =
        ∏ i : Fin n, ∑ b : Bool,
          if b = true then RetentionProbability A p α i
          else 1 - RetentionProbability A p α i := by
      simpa only [OutcomeWeight] using
        (Fintype.prod_sum (fun i (b : Bool) =>
          if b = true then RetentionProbability A p α i
          else 1 - RetentionProbability A p α i)).symm
    _ = 1 := by simp

/-- A positive exact success probability contains a simultaneously successful outcome. -/
theorem exists_embedding_of_success_pos {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α ε : ℝ)
    (h : 0 < SuccessProbability A p α ε) :
    ∃ kept : Fin n → Bool, Embedding A p α ε kept := by
  classical
  by_contra hnone
  push Not at hnone
  have hz : SuccessProbability A p α ε = 0 := by
    simp [SuccessProbability, hnone]
  exact (ne_of_gt h) hz

/-- The target's probability threshold, with `δ<1/2`, implies one successful outcome. -/
theorem exists_embedding_of_target_probability {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α ε δ : ℝ)
    (hδ : δ < 1 / 2)
    (h : 1 - δ ≤ SuccessProbability A p α ε) :
    ∃ kept : Fin n → Bool, Embedding A p α ε kept := by
  apply exists_embedding_of_success_pos A p α ε
  have hsmall : δ < 1 := by linarith
  linarith

/-- The numerical step in the source's support obstruction: if a positive
support degree obeys the witness inequality, it meets one of the two
accuracy-dependent lower bounds. -/
theorem supportDegree_lower_bound
    (p ε R k : ℝ) (hp : 0 < p) (hε : 0 < ε)
    (hR : 0 < R) (hk : 0 < k)
    (hnecessary : Real.rpow k (-p⁻¹) ≤ 4 * ε + 2 * k / R) :
    R * ε ≤ k ∨ Real.rpow (6 * ε) (-p) ≤ k := by
  by_contra h
  push Not at h
  have hsmall : k / R < ε := by
    apply (div_lt_iff₀ hR).mpr
    nlinarith [h.1]
  have hterm : 2 * k / R < 2 * ε := by
    calc
      2 * k / R = 2 * (k / R) := by ring
      _ < 2 * ε := by linarith
  have hupper : Real.rpow k (-p⁻¹) < 6 * ε := by
    linarith
  have hbase : 0 < 6 * ε := by positivity
  have hexp : -p⁻¹ < 0 := neg_neg_of_pos (inv_pos.mpr hp)
  have hpower := Real.rpow_lt_rpow_of_neg hk h.2 hexp
  have hcancel : Real.rpow (Real.rpow (6 * ε) (-p)) (-p⁻¹) = 6 * ε := by
    calc
      Real.rpow (Real.rpow (6 * ε) (-p)) (-p⁻¹) =
          Real.rpow (6 * ε) ((-p) * (-p⁻¹)) :=
        (Real.rpow_mul hbase.le (-p) (-p⁻¹)).symm
      _ = 6 * ε := by
        have hmul : -p * -p⁻¹ = (1 : ℝ) := by
          field_simp [ne_of_gt hp]
        rw [hmul, Real.rpow_eq_pow, Real.rpow_one]
  change Real.rpow (Real.rpow (6 * ε) (-p)) (-p⁻¹) <
    Real.rpow k (-p⁻¹) at hpower
  rw [hcancel] at hpower
  linarith

/-- The algebraic heart of the support-dependent potential argument. Here
`z=(1-t)^p`; the `z≤1-t` premise is the real-power inequality used in the
source. The other premise is exactly the comparison of complete and weighted
energies after the singleton-degree bounds have been applied. -/
theorem witnessEnergy_forces_degree_inequality
    (ε R k t z : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hR : 0 < R) (hk : 0 ≤ k) (ht : 0 ≤ t)
    (hz : 0 ≤ z) (hzle : z ≤ 1 - t)
    (hcompare : (1 - ε) * (2 * (R - k) + k * z) ≤
      (1 + ε) * R * (1 + z)) :
    t ≤ 4 * ε + 2 * k / R := by
  have hprod : 0 ≤ (1 - ε) * (k * z) :=
    mul_nonneg (sub_nonneg.mpr hε1) (mul_nonneg hk hz)
  have heRt : 0 ≤ ε * (R * t) :=
    mul_nonneg hε (mul_nonneg hR.le ht)
  have heK : 0 ≤ ε * k := mul_nonneg hε hk
  have hbound : R * t ≤ 4 * ε * R + 2 * k := by
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr (by linarith : 0 ≤ 1 - t - z))]
  have hdiv : t ≤ (4 * ε * R + 2 * k) / R :=
    (le_div_iff₀ hR).mpr (by nlinarith [hbound])
  have heq : (4 * ε * R + 2 * k) / R = 4 * ε + 2 * k / R := by
    field_simp [ne_of_gt hR]
  exact heq ▸ hdiv

/-- The source uses this weaker comparison after dropping the nonnegative
incident-edge term from the complete energy. -/
theorem weakWitnessEnergy_forces_degree_inequality
    (ε R k t z : ℝ) (hε : 0 ≤ ε) (hR : 0 < R)
    (hk : 0 ≤ k) (ht : 0 ≤ t) (hzle : z ≤ 1 - t)
    (hcompare : (1 - ε) * (2 * (R - k)) ≤
      (1 + ε) * R * (1 + z)) :
    t ≤ 4 * ε + 2 * k / R := by
  have heRt : 0 ≤ ε * (R * t) :=
    mul_nonneg hε (mul_nonneg hR.le ht)
  have heK : 0 ≤ ε * k := mul_nonneg hε hk
  have hbound : R * t ≤ 4 * ε * R + 2 * k := by
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr (by linarith : 0 ≤ 1 - t - z))]
  have hdiv : t ≤ (4 * ε * R + 2 * k) / R :=
    (le_div_iff₀ hR).mpr (by nlinarith [hbound])
  have heq : (4 * ε * R + 2 * k) / R = 4 * ε + 2 * k / R := by
    field_simp [ne_of_gt hR]
  exact heq ▸ hdiv

/-- The pth power used in the support witness cannot exceed its base. -/
theorem one_sub_rpow_le_one_sub
    (p t : ℝ) (hp : 1 ≤ p) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.rpow (1 - t) p ≤ 1 - t := by
  have hbase0 : 0 ≤ 1 - t := by linarith
  have hbase1 : 1 - t ≤ 1 := by linarith
  simpa only [Real.rpow_eq_pow] using
    Real.rpow_le_self_of_le_one hbase0 hbase1 hp

/-- Complete numerical support obstruction after the graph-specific
energy identities and singleton-degree estimates have been established. -/
theorem witnessComparison_forces_support_bound
    (p ε R k : ℝ) (hp : 1 < p) (hε : 0 < ε)
    (hεhalf : ε < 1 / 2) (hR : 0 < R) (hk : 1 ≤ k)
    (hcompare :
      (1 - ε) * (2 * (R - k) +
        k * Real.rpow (1 - Real.rpow k (-p⁻¹)) p) ≤
      (1 + ε) * R * (1 + Real.rpow (1 - Real.rpow k (-p⁻¹)) p)) :
    R * ε ≤ k ∨ Real.rpow (6 * ε) (-p) ≤ k := by
  let t := Real.rpow k (-p⁻¹)
  have hp0 : 0 < p := by linarith
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have ht0 : 0 ≤ t := (Real.rpow_pos_of_pos hk0 _).le
  have ht1 : t ≤ 1 := by
    dsimp [t]
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_le_one_of_one_le_of_nonpos hk (neg_nonpos.mpr (inv_pos.mpr hp0).le)
  have hz0 : 0 ≤ Real.rpow (1 - t) p :=
    Real.rpow_nonneg (by linarith : 0 ≤ 1 - t) p
  have hzle : Real.rpow (1 - t) p ≤ 1 - t :=
    one_sub_rpow_le_one_sub p t hp.le ht0 ht1
  have hnec : t ≤ 4 * ε + 2 * k / R :=
    witnessEnergy_forces_degree_inequality ε R k t
      (Real.rpow (1 - t) p) hε.le (by linarith) hR hk0.le ht0 hz0 hzle hcompare
  exact supportDegree_lower_bound p ε R k hp0 hε hR hk0 hnec

/-- The precise source-form comparison is sufficient for the support bound. -/
theorem weakWitnessComparison_forces_support_bound
    (p ε R k : ℝ) (hp : 1 < p) (hε : 0 < ε)
    (hR : 0 < R) (hk : 1 ≤ k)
    (hcompare :
      (1 - ε) * (2 * (R - k)) ≤
      (1 + ε) * R * (1 + Real.rpow (1 - Real.rpow k (-p⁻¹)) p)) :
    R * ε ≤ k ∨ Real.rpow (6 * ε) (-p) ≤ k := by
  let t := Real.rpow k (-p⁻¹)
  have hp0 : 0 < p := by linarith
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have ht0 : 0 ≤ t := (Real.rpow_pos_of_pos hk0 _).le
  have ht1 : t ≤ 1 := by
    dsimp [t]
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_le_one_of_one_le_of_nonpos hk (neg_nonpos.mpr (inv_pos.mpr hp0).le)
  have hzle : Real.rpow (1 - t) p ≤ 1 - t :=
    one_sub_rpow_le_one_sub p t hp.le ht0 ht1
  have hnec : t ≤ 4 * ε + 2 * k / R :=
    weakWitnessEnergy_forces_degree_inequality ε R k t
      (Real.rpow (1 - t) p) hε.le hR hk0.le ht0 hzle hcompare
  exact supportDegree_lower_bound p ε R k hp0 hε hR hk0 hnec

#print axioms rowEnergy_nonneg
#print axioms inputEnergy_pos
#print axioms rowEnergy_le_inputEnergy
#print axioms sensitivityRatio_mem_unit
#print axioms sensitivity_le_one
#print axioms sensitivity_le_of_rowEnergy_bound
#print axioms sensitivity_nonneg
#print axioms sensitivityRatio_le_sensitivity
#print axioms retentionProbability_pos
#print axioms retentionProbability_le_one
#print axioms outcomeWeight_nonneg
#print axioms sum_outcomeWeight_eq_one
#print axioms exists_embedding_of_success_pos
#print axioms exists_embedding_of_target_probability
#print axioms supportDegree_lower_bound
#print axioms witnessEnergy_forces_degree_inequality
#print axioms weakWitnessEnergy_forces_degree_inequality
#print axioms one_sub_rpow_le_one_sub
#print axioms witnessComparison_forces_support_bound
#print axioms weakWitnessComparison_forces_support_bound

end NLA.Proofs.RA06
