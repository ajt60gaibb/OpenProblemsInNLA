import NLA.Proofs.TR26.Wronskian

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26
open Polynomial

def affineWronskianLinear (d : ℕ) : Parameter d →ₗ[ℂ] Polynomial ℂ :=
  (Polynomial.wronskianBilin ℂ (affineDenominator d)).comp (affineNumeratorLinear d)

theorem affineWronskianLinear_apply {d : ℕ} (H : Parameter d) :
    affineWronskianLinear d H = affineWronskian H := by
  change affineDenominator d*(affineNumerator H).derivative -
    (affineDenominator d).derivative*affineNumerator H =
      (affineNumerator H).derivative*affineDenominator d -
        affineNumerator H*(affineDenominator d).derivative
  ring

def affineCriticalLinear (d : ℕ) (t : ℂ) : Parameter d →ₗ[ℂ] ℂ :=
  (Polynomial.aeval t).toLinearMap.comp (affineWronskianLinear d)

theorem affineCriticalLinear_apply {d : ℕ} (H : Parameter d) (t : ℂ) :
    affineCriticalLinear d t H = (affineWronskian H).eval t := by
  change (Polynomial.aeval t) (affineWronskianLinear d H) = _
  rw [affineWronskianLinear_apply]
  simp

theorem affineWronskian_eq_zero_iff {d : ℕ} (H : Parameter d) :
    affineWronskian H = 0 ↔ ∃ c : ℂ, affineNumerator H = C c*affineDenominator d := by
  constructor
  · intro h
    have heq : (affineNumerator H).derivative*affineDenominator d =
        affineNumerator H*(affineDenominator d).derivative := sub_eq_zero.mp h
    have hdiv : affineDenominator d ∣ affineNumerator H*(affineDenominator d).derivative := by
      rw [← heq]
      exact dvd_mul_left _ _
    have hcop : IsCoprime (affineDenominator d) (affineDenominator d).derivative :=
      affineDenominator_separable d
    have hdvd := hcop.dvd_of_dvd_mul_right hdiv
    refine ⟨(affineNumerator H).leadingCoeff, ?_⟩
    apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (affineDenominator_monic d) hdvd
    rw [affineDenominator_natDegree]
    exact affineNumerator_natDegree_le H
  · rintro ⟨c,hc⟩
    change (affineNumerator H).derivative*affineDenominator d -
      affineNumerator H*(affineDenominator d).derivative = 0
    rw [hc, derivative_C_mul]
    ring

theorem exists_affineWronskian_ne_zero {d : ℕ} (hd : 0 < d) (t : ℂ) :
    ∃ H : Parameter d, (affineWronskian H).eval t ≠ 0 := by
  by_cases hD : (affineDenominator d).eval t = 0
  · obtain ⟨H,hH⟩ := affineNumerator_surjective_degreeLE d 1 (by simp)
    refine ⟨H, ?_⟩
    have hder := denominator_derivative_at_root_ne_zero ((mem_denominatorRoots_iff d t).mpr hD)
    change eval t ((affineNumerator H).derivative*affineDenominator d -
      affineNumerator H*(affineDenominator d).derivative) ≠ 0
    simpa [hH] using neg_ne_zero.mpr hder
  · obtain ⟨H,hH⟩ := affineNumerator_surjective_degreeLE d (X-C t)
      (by rw [natDegree_X_sub_C]; omega)
    refine ⟨H, ?_⟩
    change eval t ((affineNumerator H).derivative*affineDenominator d -
      affineNumerator H*(affineDenominator d).derivative) ≠ 0
    simpa [hH] using hD

theorem exists_affineCritical_pivot {d : ℕ} (hd : 0 < d) (t : ℂ) :
    ∃ j : SymIndex d, affineCriticalLinear d t (Pi.single j 1) ≠ 0 := by
  classical
  obtain ⟨H,hH⟩ := exists_affineWronskian_ne_zero hd t
  by_contra! hbad
  have hrep : H = ∑ j : SymIndex d, H j • Pi.single j 1 := by
    ext j
    simp [Pi.single_apply]
  have hz : affineCriticalLinear d t H = 0 := by
    rw [hrep, map_sum]
    simp only [map_smul, hbad, smul_zero, Finset.sum_const_zero]
  rw [affineCriticalLinear_apply] at hz
  exact hH hz

#assert_trust kernel affineWronskian_eq_zero_iff
#assert_trust kernel exists_affineWronskian_ne_zero
#assert_trust kernel exists_affineCritical_pivot
#print axioms exists_affineCritical_pivot
end NLA.Proofs.TR26
