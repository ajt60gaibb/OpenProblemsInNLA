import Mathlib
import LeanCert.Tactic.Verification
import NLA.Proofs.MF03.CosineTail
import NLA.Proofs.MF03.WaveAtThree

/-!
The analytic series and product interface from the independently reviewed
MF-03 cosine-product contract. The product identity remains a separate proof
obligation; this module starts with the exact normalization and real-value
bridges.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.MF03

/-- The same entire series whose coefficients define the frozen Padé target. -/
noncomputable def waveSeries (z : ℂ) : ℂ :=
  ∑' j : ℕ, z ^ j / (((2 * j).factorial : ℕ) : ℂ)

/-- The first `N` factors of the manuscript's positive-factor product. -/
noncomputable def cosinePartialProduct (N : ℕ) (z : ℂ) : ℂ :=
  ∏ k ∈ Finset.range N, ((1 : ℂ) + (cosineFactor (k + 1) : ℂ) * z)

private theorem cosineFactors_summable :
    Summable (fun k : ℕ => cosineFactor (k + 1)) := by
  have hbase : Summable (fun k : ℕ =>
      1 / |(k : ℝ) + 1 / 2| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow (1 / 2) 2).2 (by norm_num)
  have hbase' : Summable (fun k : ℕ =>
      1 / |(k : ℝ) + 1 / 2| ^ (2 : ℕ)) := by
    simpa only [Real.rpow_two] using hbase
  have hscale := hbase'.mul_left (1 / Real.pi ^ 2)
  apply hscale.congr
  intro k
  have hcast : (((k + 1 : ℕ) : ℝ) - 1 / 2) = (k : ℝ) + 1 / 2 := by
    push_cast
    ring
  have hpos : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
  have hfactor : cosineFactor (k + 1) =
      1 / (Real.pi ^ 2 * ((k : ℝ) + 1 / 2) ^ 2) := by
    unfold cosineFactor
    rw [hcast]
  rw [hfactor, abs_of_pos hpos, one_div_mul_one_div]

/-- Every complex specialization has a genuine convergent positive-factor product. -/
theorem cosineFactors_multipliable (z : ℂ) :
    Multipliable (fun k : ℕ =>
      (1 : ℂ) + (cosineFactor (k + 1) : ℂ) * z) := by
  apply multipliable_one_add_of_summable
  have hs := cosineFactors_summable.mul_left ‖z‖
  apply hs.congr
  intro k
  have hnonneg : 0 ≤ cosineFactor (k + 1) := by
    unfold cosineFactor
    positivity
  simp [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hnonneg, mul_comm]

theorem waveSeries_zero : waveSeries 0 = 1 := by
  unfold waveSeries
  rw [tsum_eq_single 0]
  · norm_num
  · intro j hj
    simp [hj]

theorem waveSeries_three_eq_waveAtThree :
    waveSeries (3 : ℂ) = (waveAtThree : ℂ) := by
  rw [waveSeries, waveAtThree, Complex.ofReal_tsum]
  congr 1
  funext j
  push_cast
  rfl

#assert_trust kernel waveSeries_zero
#assert_trust kernel waveSeries_three_eq_waveAtThree
#assert_trust kernel cosineFactors_multipliable
#print axioms waveSeries_three_eq_waveAtThree
#print axioms cosineFactors_multipliable

end NLA.Proofs.MF03
