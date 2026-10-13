import NLA.Statements.MF03
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-! Cancellation of common polynomial factors in a normalized MF-03 Padé pair. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

open NLA.Statements.MF03

private noncomputable def waveSeries : PowerSeries ℂ :=
  PowerSeries.mk fun j => 1 / ((2 * j).factorial : ℂ)

private theorem normalized_coeff_powerSeries
    (m : ℕ) (P Q : Polynomial ℂ)
    (h : NormalizedPadeRepresentation m P Q)
    (j : ℕ) (hj : j ≤ 2 * m) :
    PowerSeries.coeff j ((Q : PowerSeries ℂ) * waveSeries) =
      PowerSeries.coeff j (P : PowerSeries ℂ) := by
  have hcoef := h.2.2.2 j hj
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa only [Polynomial.coeff_coe, PowerSeries.coeff_mk, waveSeries,
    div_eq_mul_inv, one_mul, Nat.succ_eq_add_one] using hcoef

private theorem coeff_zero_of_mul_right
    (D S : PowerSeries ℂ) (hD : PowerSeries.coeff 0 D ≠ 0)
    (N : ℕ) (hprod : ∀ j : ℕ, j ≤ N →
      PowerSeries.coeff j (S * D) = 0) :
    ∀ j : ℕ, j ≤ N → PowerSeries.coeff j S = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj
      have h := hprod j hj
      rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ] at h
      have hsum :
          (∑ i ∈ Finset.range j,
            PowerSeries.coeff i S * PowerSeries.coeff (j - i) D) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        rw [ih i hij (Nat.le_trans (Nat.le_of_lt hij) hj)]
        simp
      rw [hsum, zero_add, Nat.sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right hD

private theorem coeff_eq_of_factor
    (D A B : PowerSeries ℂ) (hD : PowerSeries.coeff 0 D ≠ 0)
    (N : ℕ) (h : ∀ j : ℕ, j ≤ N →
      PowerSeries.coeff j (D * A) = PowerSeries.coeff j (D * B)) :
    ∀ j : ℕ, j ≤ N → PowerSeries.coeff j A = PowerSeries.coeff j B := by
  have hz : ∀ j : ℕ, j ≤ N →
      PowerSeries.coeff j ((A - B) * D) = 0 := by
    intro j hj
    rw [sub_mul, map_sub, mul_comm A D, mul_comm B D,
      h j hj, sub_self]
  have hzero := coeff_zero_of_mul_right D (A - B) hD N hz
  intro j hj
  have hjzero := hzero j hj
  rw [map_sub, sub_eq_zero] at hjzero
  exact hjzero

/-- Every normalized Padé pair has a reduced normalized representative of the
same rational function. -/
theorem normalized_exists_reduced
    (m : ℕ) (P Q : Polynomial ℂ)
    (h : NormalizedPadeRepresentation m P Q) :
    ∃ Pᵣ Qᵣ : Polynomial ℂ,
      ReducedPadeRepresentation m Pᵣ Qᵣ ∧ Pᵣ * Q = P * Qᵣ := by
  let D : Polynomial ℂ := GCDMonoid.gcd P Q
  let P₁ : Polynomial ℂ := P / D
  let Q₁ : Polynomial ℂ := Q / D
  let c : ℂ := D.eval 0
  have hQne : Q ≠ 0 := by
    intro hzero
    have hQzero := h.2.2.1
    simp [hzero] at hQzero
  have hPzero : P.coeff 0 = 1 := by
    have hzero := h.2.2.2 0 (by omega)
    have hQzero : Q.coeff 0 = 1 := by
      simpa only [Polynomial.coeff_zero_eq_eval_zero] using h.2.2.1
    norm_num [Finset.sum_range_succ, hQzero] at hzero ⊢
    exact hzero.symm
  have hPne : P ≠ 0 := by
    intro hzero
    simp [hzero] at hPzero
  have hDne : D ≠ 0 := gcd_ne_zero_of_right hQne
  have hDP : D ∣ P := GCDMonoid.gcd_dvd_left P Q
  have hDQ : D ∣ Q := GCDMonoid.gcd_dvd_right P Q
  have hPfac : D * P₁ = P := EuclideanDomain.mul_div_cancel' hDne hDP
  have hQfac : D * Q₁ = Q := EuclideanDomain.mul_div_cancel' hDne hDQ
  have hcQ : c * Q₁.eval 0 = 1 := by
    calc
      c * Q₁.eval 0 = (D * Q₁).eval 0 := by simp [c]
      _ = 1 := by rw [hQfac]; exact h.2.2.1
  have hcne : c ≠ 0 := left_ne_zero_of_mul_eq_one hcQ
  have hcunit : IsUnit (Polynomial.C c) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcne)
  have hP₁deg : P₁.natDegree ≤ m := by
    have hdvd : P₁ ∣ P := ⟨D, by rw [mul_comm, hPfac]⟩
    exact (Polynomial.natDegree_le_of_dvd hdvd hPne).trans h.1
  have hQ₁deg : Q₁.natDegree ≤ m := by
    have hdvd : Q₁ ∣ Q := ⟨D, by rw [mul_comm, hQfac]⟩
    exact (Polynomial.natDegree_le_of_dvd hdvd hQne).trans h.2.1
  have hcop : IsCoprime P₁ Q₁ := isCoprime_div_gcd_div_gcd hQne
  have hDcoeff : PowerSeries.coeff 0 (D : PowerSeries ℂ) ≠ 0 := by
    simpa only [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero] using hcne
  have hquotseries : ∀ j : ℕ, j ≤ 2 * m →
      PowerSeries.coeff j ((Q₁ : PowerSeries ℂ) * waveSeries) =
        PowerSeries.coeff j (P₁ : PowerSeries ℂ) := by
    apply coeff_eq_of_factor (D : PowerSeries ℂ)
      ((Q₁ : PowerSeries ℂ) * waveSeries) (P₁ : PowerSeries ℂ)
      hDcoeff (2 * m)
    intro j hj
    have hnorm := normalized_coeff_powerSeries m P Q h j hj
    have hleft :
        ((D : PowerSeries ℂ) * ((Q₁ : PowerSeries ℂ) * waveSeries)) =
          ((Q : PowerSeries ℂ) * waveSeries) := by
      rw [← mul_assoc, ← Polynomial.coe_mul, hQfac]
    have hright :
        (D : PowerSeries ℂ) * (P₁ : PowerSeries ℂ) =
          (P : PowerSeries ℂ) := by
      rw [← Polynomial.coe_mul, hPfac]
    rwa [hleft, hright]
  have hquotcoeff : ∀ j : ℕ, j ≤ 2 * m →
      (∑ i ∈ Finset.range (j + 1),
        Q₁.coeff i / ((2 * (j - i)).factorial : ℂ)) = P₁.coeff j := by
    intro j hj
    have hseries := hquotseries j hj
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hseries
    simpa only [Polynomial.coeff_coe, PowerSeries.coeff_mk, waveSeries,
      div_eq_mul_inv, one_mul, Nat.succ_eq_add_one] using hseries
  refine ⟨Polynomial.C c * P₁, Polynomial.C c * Q₁, ?_, ?_⟩
  · constructor
    · refine ⟨(Polynomial.natDegree_C_mul_le c P₁).trans hP₁deg,
        (Polynomial.natDegree_C_mul_le c Q₁).trans hQ₁deg, ?_, ?_⟩
      · simpa [c] using hcQ
      · intro j hj
        simpa only [Polynomial.coeff_C_mul, ← Finset.mul_sum,
          mul_div_assoc] using congrArg (fun x : ℂ => c * x) (hquotcoeff j hj)
    · exact (isCoprime_mul_unit_left hcunit P₁ Q₁).2 hcop
  · calc
      (Polynomial.C c * P₁) * Q = (Polynomial.C c * P₁) * (D * Q₁) := by rw [hQfac]
      _ = (D * P₁) * (Polynomial.C c * Q₁) := by ring
      _ = P * (Polynomial.C c * Q₁) := by rw [hPfac]

#print axioms normalized_exists_reduced
#assert_trust kernel normalized_exists_reduced

end NLA.Proofs.MF03
