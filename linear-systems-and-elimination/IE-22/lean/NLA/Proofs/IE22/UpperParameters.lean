import NLA.Proofs.IE22.GaussianBasics

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.IE22

/-- One small fixed tolerance, then one fixed deletion count, then sufficiently
large ambient dimensions make both genuine probability errors and normalization
inflation small. The finite mesh size precedes the deletion count. -/
theorem exists_upper_parameters (ε : ℝ) (hε : 0 < ε) (L K : ℝ)
    (hL : 0 ≤ L) (hK : 0 ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ M : ℕ, ∃ r N : ℕ,
      ∀ n : ℕ, N ≤ n → r < n ∧
        (1/4 : ℝ)+(M : ℝ)*(4*L/(Real.sqrt (r+1 : ℕ)*δ^2))+
          K/((n-r : ℕ)*δ^2) < 1 ∧
        ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
          (n : ℝ)/((1-δ)*(n-r : ℕ))*(h+3*δ) ≤ h+ε := by
  let δ := min (ε/16) (1/16 : ℝ)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ16 : δ ≤ (1/16 : ℝ) := min_le_right _ _
  have hδε : δ ≤ ε/16 := min_le_left _ _
  have hδ1 : δ < 1 := lt_of_le_of_lt hδ16 (by norm_num)
  have hδsq : 0 < δ^2 := sq_pos_of_pos hδ
  refine ⟨δ,hδ,hδ1,?_⟩
  intro M
  let C := 16*L*(M : ℝ)/δ^2+1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨r,hr⟩ := exists_nat_gt (C^2)
  have hrD : (0 : ℝ) < (r+1 : ℕ) := by positivity
  have hsqrt : C < Real.sqrt (r+1 : ℕ) := by
    have hroot := Real.sq_sqrt hrD.le
    have hroot0 := Real.sqrt_nonneg (r+1 : ℕ)
    have hcast : (r+1 : ℕ) = (r : ℝ)+1 := by norm_cast
    nlinarith
  have hR : (M : ℝ)*(4*L/(Real.sqrt (r+1 : ℕ)*δ^2)) < 1/4 := by
    have hd : 0 < Real.sqrt (r+1 : ℕ)*δ^2 := mul_pos (Real.sqrt_pos.2 hrD) hδsq
    have hCeq : C*δ^2 = 16*L*(M : ℝ)+δ^2 := by dsimp [C]; field_simp
    have hmul := mul_lt_mul_of_pos_right hsqrt hδsq
    rw [hCeq] at hmul
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hd).2
    nlinarith
  obtain ⟨D,hD⟩ := exists_nat_gt (max ((r : ℝ)/δ) (max (4*K/δ^2) (1 : ℝ)))
  have hDr : (r : ℝ)/δ < D := lt_of_le_of_lt (le_max_left _ _) hD
  have hDK : 4*K/δ^2 < D := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hD
  have hD1 : (1 : ℝ) < D := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hD
  have hD0 : 0 < D := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hD1)
  refine ⟨r,r+D,?_⟩
  intro n hn
  have hrn : r < n := by omega
  have hDd : D ≤ n-r := by omega
  have hdR : (0 : ℝ) < (n-r : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hrn)
  have hDdR : (D : ℝ) ≤ (n-r : ℕ) := by exact_mod_cast hDd
  have hNorm : K/((n-r : ℕ)*δ^2) < 1/4 := by
    apply (div_lt_iff₀ (mul_pos hdR hδsq)).2
    have h4 := (div_lt_iff₀ hδsq).1 hDK
    have hmono := mul_le_mul_of_nonneg_right hDdR hδsq.le
    nlinarith
  refine ⟨hrn, by linarith [hR,hNorm], ?_⟩
  intro h hh0 hh1
  have hδd : (r : ℝ) ≤ δ*(n-r : ℕ) := by
    have h := (div_lt_iff₀ hδ).1 hDr
    have hmono := mul_le_mul_of_nonneg_right hDdR hδ.le
    nlinarith
  have hnd : (n : ℝ) = (n-r : ℕ)+(r : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel hrn.le).symm
  have hnratio : (n : ℝ) ≤ (1+δ)*(n-r : ℕ) := by nlinarith
  have h1δ : 0 < 1-δ := sub_pos.mpr hδ1
  have hfactor : (n : ℝ)/((1-δ)*(n-r : ℕ)) ≤ (1+δ)/(1-δ) := by
    apply (div_le_div_iff₀ (mul_pos h1δ hdR) h1δ).2
    have h := mul_le_mul_of_nonneg_right hnratio h1δ.le
    nlinarith
  calc
    _ ≤ ((1+δ)/(1-δ))*(h+3*δ) :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ ≤ _ := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ h1δ).2
      have hdh : δ*h ≤ δ := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hh1)]
      have hde : δ*ε ≤ ε/16 := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hδ16)]
      have hd2 : δ^2 ≤ δ/16 := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ16)]
      nlinarith

#assert_trust kernel exists_upper_parameters
#print axioms exists_upper_parameters
end NLA.Proofs.IE22
