import NLA.Statements.MF03
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-! Uniqueness of the rational function encoded by the MF-03 Padé equations. -/
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

private theorem coeff_mul_eq_of_coeff_eq_below
    (S T U : PowerSeries ℂ) (N j : ℕ)
    (h : ∀ i ≤ N, PowerSeries.coeff i S = PowerSeries.coeff i T)
    (hj : j ≤ N) :
    PowerSeries.coeff j (S * U) = PowerSeries.coeff j (T * U) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hleft : ij.1 ≤ j := by
    have hsum := Finset.mem_antidiagonal.mp hij
    omega
  rw [h ij.1 (hleft.trans hj)]

/-- Two normalized diagonal Padé pairs of the same order encode the same
rational function, even before common factors are cancelled. -/
theorem normalized_cross_product_eq
    (m : ℕ) (P₁ Q₁ P₂ Q₂ : Polynomial ℂ)
    (h₁ : NormalizedPadeRepresentation m P₁ Q₁)
    (h₂ : NormalizedPadeRepresentation m P₂ Q₂) :
    P₁ * Q₂ = P₂ * Q₁ := by
  have hdeg₁ : (P₁ * Q₂).natDegree ≤ 2 * m := by
    have hm : (P₁ * Q₂).natDegree ≤ P₁.natDegree + Q₂.natDegree :=
      Polynomial.natDegree_mul_le
    have hp := h₁.1
    have hq := h₂.2.1
    omega
  have hdeg₂ : (P₂ * Q₁).natDegree ≤ 2 * m := by
    have hm : (P₂ * Q₁).natDegree ≤ P₂.natDegree + Q₁.natDegree :=
      Polynomial.natDegree_mul_le
    have hp := h₂.1
    have hq := h₁.2.1
    omega
  apply (Polynomial.ext_iff_natDegree_le hdeg₁ hdeg₂).2
  intro j hj
  have hfirst := coeff_mul_eq_of_coeff_eq_below
    (P₁ : PowerSeries ℂ) ((Q₁ : PowerSeries ℂ) * waveSeries)
    (Q₂ : PowerSeries ℂ) (2 * m) j
    (fun i hi => (normalized_coeff_powerSeries m P₁ Q₁ h₁ i hi).symm) hj
  have hsecond := coeff_mul_eq_of_coeff_eq_below
    ((Q₂ : PowerSeries ℂ) * waveSeries) (P₂ : PowerSeries ℂ)
    (Q₁ : PowerSeries ℂ) (2 * m) j
    (fun i hi => normalized_coeff_powerSeries m P₂ Q₂ h₂ i hi) hj
  have hreorder :
      ((Q₁ : PowerSeries ℂ) * waveSeries) * (Q₂ : PowerSeries ℂ) =
        ((Q₂ : PowerSeries ℂ) * waveSeries) * (Q₁ : PowerSeries ℂ) := by
    ring
  calc
    (P₁ * Q₂).coeff j =
        PowerSeries.coeff j ((P₁ : PowerSeries ℂ) * (Q₂ : PowerSeries ℂ)) := by
          simp only [← Polynomial.coe_mul, Polynomial.coeff_coe]
    _ = PowerSeries.coeff j (((Q₁ : PowerSeries ℂ) * waveSeries) *
        (Q₂ : PowerSeries ℂ)) := hfirst
    _ = PowerSeries.coeff j (((Q₂ : PowerSeries ℂ) * waveSeries) *
        (Q₁ : PowerSeries ℂ)) := by rw [hreorder]
    _ = PowerSeries.coeff j ((P₂ : PowerSeries ℂ) * (Q₁ : PowerSeries ℂ)) :=
      hsecond
    _ = (P₂ * Q₁).coeff j := by
      simp only [← Polynomial.coe_mul, Polynomial.coeff_coe]

#print axioms normalized_cross_product_eq
#assert_trust kernel normalized_cross_product_eq

end NLA.Proofs.MF03
