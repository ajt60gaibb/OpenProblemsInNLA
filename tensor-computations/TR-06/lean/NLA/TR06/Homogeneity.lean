/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators ENNReal
namespace NLA.TR06

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- For a positive-order tensor, scalar multiplication can be absorbed into
one factor. The order condition is necessary for this factor representation. -/
theorem pureTensor_smul (hd : 0 < d) (u : (j : Fin d) → Fin (n j) → ℝ) (t : ℝ) :
    ∃ v : (j : Fin d) → Fin (n j) → ℝ, pureTensor v = t • pureTensor u := by
  let j₀ : Fin d := ⟨0, hd⟩
  refine ⟨Function.update u j₀ (t • u j₀), ?_⟩
  ext q
  change (∏ j, Function.update u j₀ (t • u j₀) j (q j)) = t * ∏ j, u j (q j)
  have heq : (∏ j ∈ Finset.univ \ {j₀}, Function.update u j₀ (t • u j₀) j (q j)) =
      ∏ j ∈ Finset.univ \ {j₀}, u j (q j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hne : j ≠ j₀ := fun h => (Finset.mem_sdiff.mp hj).2 (Finset.mem_singleton.mpr h)
    rw [Function.update_of_ne hne]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j₀),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j₀)]
  rw [heq]
  simp only [Function.update_self, Pi.smul_apply, smul_eq_mul]
  ring

/-- Nonzero scaling preserves actual nonzero rank-one tensors. -/
theorem rankOne_smul (hd : 0 < d) {A : Tensor ℝ d n} (hA : RankOne A)
    {t : ℝ} (ht : t ≠ 0) : RankOne (t • A) := by
  refine ⟨smul_ne_zero ht hA.1, ?_⟩
  obtain ⟨u, rfl⟩ := hA.2
  exact pureTensor_smul hd u t

/-- Scaling every summand scales the reconstructed tensor. -/
theorem decomposes_smul (hd : 0 < d) {a : Fin r → Tensor ℝ d n} {A : Tensor ℝ d n}
    (ha : Decomposes a A) {t : ℝ} (ht : t ≠ 0) :
    Decomposes (fun i => t • a i) (t • A) := by
  exact ⟨fun i => rankOne_smul hd (ha.1 i) ht, by rw [← Finset.smul_sum, ha.2]⟩

/-- Existence of a fixed-length decomposition is invariant under nonzero scaling. -/
theorem exists_decomposes_smul_iff (hd : 0 < d) (A : Tensor ℝ d n)
    {t : ℝ} (ht : t ≠ 0) (m : ℕ) :
    (∃ a : Fin m → Tensor ℝ d n, Decomposes a (t • A)) ↔
      ∃ a : Fin m → Tensor ℝ d n, Decomposes a A := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun i => t⁻¹ • a i, ?_⟩
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using
      decomposes_smul hd ha (inv_ne_zero ht)
  · rintro ⟨a, ha⟩
    exact ⟨fun i => t • a i, decomposes_smul hd ha ht⟩

/-- The original exact real rank, including exclusion of every shorter
nonzero-summand representation, is preserved by scaling. -/
theorem exactRank_smul_iff (hd : 0 < d) (A : Tensor ℝ d n)
    {t : ℝ} (ht : t ≠ 0) : ExactRank r (t • A) ↔ ExactRank r A := by
  simp only [ExactRank, exists_decomposes_smul_iff hd A ht]

theorem identifiable_smul (hd : 0 < d) {A : Tensor ℝ d n}
    (hA : Identifiable r A) {t : ℝ} (ht : t ≠ 0) : Identifiable r (t • A) := by
  intro a b ha hb
  have ha' : Decomposes (fun i => t⁻¹ • a i) A := by
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using
      decomposes_smul hd ha (inv_ne_zero ht)
  have hb' : Decomposes (fun i => t⁻¹ • b i) A := by
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using
      decomposes_smul hd hb (inv_ne_zero ht)
  obtain ⟨σ, hσ⟩ := hA _ _ ha' hb'
  refine ⟨σ, fun i => ?_⟩
  have heq := congrArg (fun x : Tensor ℝ d n => t • x) (hσ i)
  simpa only [smul_smul, mul_inv_cancel₀ ht, one_smul] using heq

theorem identifiable_smul_iff (hd : 0 < d) (A : Tensor ℝ d n)
    {t : ℝ} (ht : t ≠ 0) : Identifiable r (t • A) ↔ Identifiable r A := by
  constructor
  · intro h
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using
      identifiable_smul hd h (inv_ne_zero ht)
  · exact fun h => identifiable_smul hd h ht

theorem smul_mem_identifiableRealSet_iff (hd : 0 < d) (A : Tensor ℝ d n)
    {t : ℝ} (ht : t ≠ 0) :
    t • A ∈ identifiableRealSet d n r ↔ A ∈ identifiableRealSet d n r := by
  exact and_congr (exactRank_smul_iff hd A ht) (identifiable_smul_iff hd A ht)

/-- Individual normalization removes a positive common scale exactly. -/
theorem normalizedTuple_pos_smul (a : Fin r → Tensor ℝ d n)
    {t : ℝ} (ht : 0 < t) : normalizedTuple (fun i => t • a i) = normalizedTuple a := by
  ext q
  change (t * a q.1 q.2) / ‖t • a q.1‖ = a q.1 q.2 / ‖a q.1‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  exact mul_div_mul_left _ _ ht.ne'

private theorem angularDistance_pos_smul_le (hd : 0 < d) (A B : Tensor ℝ d n)
    {t : ℝ} (ht : 0 < t) : angularDistance r (t • A) (t • B) ≤ angularDistance r A B := by
  unfold angularDistance
  refine le_iInf fun a => le_iInf fun ha => le_iInf fun b => le_iInf fun hb => ?_
  refine iInf_le_of_le (fun i => t • a i) (iInf_le_of_le
    (decomposes_smul hd ha ht.ne') (iInf_le_of_le (fun i => t • b i)
      (iInf_le_of_le (decomposes_smul hd hb ht.ne') ?_)))
  simp only [normalizedTuple_pos_smul _ ht, le_rfl]

/-- The unordered normalized output distance is invariant under a positive
common scale, with no choice of decomposition or local branch. -/
theorem angularDistance_pos_smul (hd : 0 < d) (A B : Tensor ℝ d n)
    {t : ℝ} (ht : 0 < t) : angularDistance r (t • A) (t • B) = angularDistance r A B := by
  refine le_antisymm (angularDistance_pos_smul_le hd A B ht) ?_
  simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using
    angularDistance_pos_smul_le (r := r) hd (t • A) (t • B) (inv_pos.mpr ht)

/-- The local angular quotient has exactly inverse radial scaling. -/
theorem angularRatio_pos_smul (hd : 0 < d) (A B : Tensor ℝ d n)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t * (angularDistance r (t • A) (t • B) / edist (t • A) (t • B)) =
      angularDistance r A B / edist A B := by
  rw [angularDistance_pos_smul hd A B ht]
  simp only [edist_dist, dist_smul₀, Real.norm_eq_abs, abs_of_pos ht,
    ENNReal.ofReal_mul ht.le]
  rw [← mul_div_assoc]
  exact ENNReal.mul_div_mul_left _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr ht))
    ENNReal.ofReal_ne_top

private theorem angularSlope_pos_smul_mul_le (hd : 0 < d) (A : Tensor ℝ d n)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t * angularSlope r (t • A) ≤ angularSlope r A := by
  unfold angularSlope
  refine le_iInf fun ε => le_iInf fun hε => ?_
  calc
    ENNReal.ofReal t * (⨅ (δ : ℝ) (_ : 0 < δ),
        ⨆ (B : Tensor ℝ d n) (_ : B ∈ identifiableRealSet d n r)
          (_ : B ≠ t • A) (_ : dist (t • A) B < δ),
          angularDistance r (t • A) B / edist (t • A) B) ≤
        ENNReal.ofReal t * (⨆ (B : Tensor ℝ d n) (_ : B ∈ identifiableRealSet d n r)
          (_ : B ≠ t • A) (_ : dist (t • A) B < t * ε),
          angularDistance r (t • A) B / edist (t • A) B) :=
      mul_le_mul' le_rfl (iInf_le_of_le (t * ε) (iInf_le _ (mul_pos ht hε)))
    _ ≤ ⨆ (B : Tensor ℝ d n) (_ : B ∈ identifiableRealSet d n r)
          (_ : B ≠ A) (_ : dist A B < ε), angularDistance r A B / edist A B := by
      simp only [ENNReal.mul_iSup]
      refine iSup_le fun B => iSup_le fun hB => iSup_le fun hne => iSup_le fun hdist => ?_
      let C := t⁻¹ • B
      have hBC : t • C = B := by simp [C, smul_smul, ht.ne']
      have hC : C ∈ identifiableRealSet d n r :=
        (smul_mem_identifiableRealSet_iff hd B (inv_ne_zero ht.ne')).mpr hB
      have hCA : C ≠ A := by
        intro heq
        apply hne
        rw [← hBC, heq]
      have hCdist : dist A C < ε := by
        rw [← hBC, dist_smul₀, Real.norm_eq_abs, abs_of_pos ht] at hdist
        exact (mul_lt_mul_iff_right₀ ht).mp hdist
      rw [← hBC, angularRatio_pos_smul hd A C ht]
      exact le_iSup_of_le C (le_iSup_of_le hC
        (le_iSup_of_le hCA (le_iSup_of_le hCdist le_rfl)))

/-- Exact radial homogeneity of the intrinsic angular slope, including
extended values and all exceptional points in the original definition. -/
theorem angularSlope_pos_smul (hd : 0 < d) (A : Tensor ℝ d n)
    {t : ℝ} (ht : 0 < t) :
    angularSlope r (t • A) = angularSlope r A / ENNReal.ofReal t := by
  have ht0 : ENNReal.ofReal t ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr ht)
  have hle := angularSlope_pos_smul_mul_le (r := r) hd A ht
  have hge := angularSlope_pos_smul_mul_le (r := r) hd (t • A) (inv_pos.mpr ht)
  simp only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul,
    ENNReal.ofReal_inv_of_pos ht] at hge
  have hge' := mul_le_mul' (le_refl (ENNReal.ofReal t)) hge
  rw [← mul_assoc, ENNReal.mul_inv_cancel ht0 ENNReal.ofReal_ne_top, one_mul] at hge'
  apply (ENNReal.eq_div_iff ht0 ENNReal.ofReal_ne_top).2
  exact le_antisymm hle hge'

#print axioms angularSlope_pos_smul
#assert_trust kernel angularSlope_pos_smul

#print axioms angularDistance_pos_smul
#print axioms smul_mem_identifiableRealSet_iff
#assert_trust kernel angularDistance_pos_smul
#assert_trust kernel smul_mem_identifiableRealSet_iff

#print axioms pureTensor_smul
#print axioms rankOne_smul
#print axioms decomposes_smul
#assert_trust kernel pureTensor_smul
#assert_trust kernel rankOne_smul
#assert_trust kernel decomposes_smul
end NLA.TR06
