import NLA.Proofs.SP14.EndpointAbsoluteKernel
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries

/-!
The exact scalar Hilbert–Schmidt column series for the source's triangular
endpoint inverse. Matrix energy and circle Parseval are separate gates.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open MeasureTheory

/-- Squared Hilbert–Schmidt mass of source inverse column `k`. -/
noncomputable def endpointInverseHSColumn (r : ℝ) (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ) ^ (-2 * r)) *
    ∑ l ∈ Finset.range (k + 1), endpointCentralCoeff l ^ 2

/-- The exact squared Hilbert–Schmidt sum, before any majorization. -/
noncomputable def endpointInverseHSSquare (r : ℝ) : ℝ :=
  ∑' k : ℕ, endpointInverseHSColumn r k

/-- Explicit sufficient source inverse bound for every `r > 1/2`. -/
noncomputable def endpointInverseHSBound (r : ℝ) : ℝ :=
  1 + 1 / (r - 1 / 2)

private theorem endpointCentralCoeff_partial_le_harmonic (k : ℕ) :
    (∑ l ∈ Finset.range (k + 1), endpointCentralCoeff l ^ 2) ≤
      (harmonic (k + 1) : ℝ) := by
  rw [harmonic]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum
  intro l hl
  have hpos : (0 : ℝ) < ((l + 1 : ℕ) : ℝ) := by positivity
  have hbound := endpointCentralCoeff_sq_bound l
  have hh : endpointCentralCoeff l ^ 2 ≤ 1 / (((l + 1 : ℕ) : ℝ)) := by
    apply (le_div_iff₀ hpos).2
    nlinarith [hbound]
  simpa only [one_div] using hh

private theorem endpointInverseHS_inner_le_power (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (k : ℕ) :
    (∑ l ∈ Finset.range (k + 1), endpointCentralCoeff l ^ 2) ≤
      endpointInverseHSBound r * (((k + 1 : ℕ) : ℝ) ^ (r - 1 / 2)) := by
  let δ : ℝ := r - 1 / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hn : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
  have hpow : 1 ≤ (((k + 1 : ℕ) : ℝ) ^ δ) := Real.one_le_rpow hn hδ.le
  have hlog : Real.log (((k + 1 : ℕ) : ℝ)) ≤
      (((k + 1 : ℕ) : ℝ) ^ δ) / δ :=
    Real.log_le_rpow_div (by positivity) hδ
  have h1 :
      (∑ l ∈ Finset.range (k + 1), endpointCentralCoeff l ^ 2) ≤
        1 + Real.log (((k + 1 : ℕ) : ℝ)) :=
    (endpointCentralCoeff_partial_le_harmonic k).trans
      (harmonic_le_one_add_log (k + 1))
  have h2 : 1 + Real.log (((k + 1 : ℕ) : ℝ)) ≤
      (1 + 1 / δ) * (((k + 1 : ℕ) : ℝ) ^ δ) := by
    calc
      1 + Real.log (((k + 1 : ℕ) : ℝ)) ≤
          1 + (((k + 1 : ℕ) : ℝ) ^ δ) / δ := by
            simpa only [add_comm] using add_le_add_left hlog 1
      _ ≤ (((k + 1 : ℕ) : ℝ) ^ δ) +
          (((k + 1 : ℕ) : ℝ) ^ δ) / δ := by
            simpa only [add_comm] using
              add_le_add_right hpow ((((k + 1 : ℕ) : ℝ) ^ δ) / δ)
      _ = (1 + 1 / δ) * (((k + 1 : ℕ) : ℝ) ^ δ) := by ring
  exact h1.trans (by simpa only [endpointInverseHSBound, δ] using h2)

private theorem endpointInverseHSColumn_le_pseries (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (k : ℕ) :
    endpointInverseHSColumn r k ≤
      endpointInverseHSBound r *
        (((k + 1 : ℕ) : ℝ) ^ (-(r + 1 / 2))) := by
  let x : ℝ := ((k + 1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hinner := endpointInverseHS_inner_le_power r hrHalf k
  have hmul := mul_le_mul_of_nonneg_left hinner
    (Real.rpow_nonneg hx.le (-2 * r))
  unfold endpointInverseHSColumn at hmul ⊢
  calc
    x ^ (-2 * r) *
        (∑ l ∈ Finset.range (k + 1), endpointCentralCoeff l ^ 2) ≤
      x ^ (-2 * r) * (endpointInverseHSBound r * x ^ (r - 1 / 2)) := hmul
    _ = endpointInverseHSBound r * x ^ (-(r + 1 / 2)) := by
      rw [← mul_assoc, mul_comm (x ^ (-2 * r)), mul_assoc, ← Real.rpow_add hx]
      congr 1
      ring

private theorem endpointInversePSeries_summable (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) :
    Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-(r + 1 / 2)))) := by
  have h : Summable (fun k : ℕ => (k : ℝ) ^ (-(r + 1 / 2))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  simpa [Nat.cast_add] using (summable_nat_add_iff 1).2 h

/-- The exact source Hilbert–Schmidt scalar series converges for all `r>1/2`. -/
theorem summable_endpointInverseHSColumn (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) :
    Summable (endpointInverseHSColumn r) := by
  apply Summable.of_nonneg_of_le
    (fun k => by unfold endpointInverseHSColumn; positivity)
    (fun k => endpointInverseHSColumn_le_pseries r hrHalf k)
  exact (endpointInversePSeries_summable r hrHalf).mul_left _

private theorem endpointInversePSeries_tsum_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) :
    (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(r + 1 / 2)))) ≤
      endpointInverseHSBound r := by
  let p : ℝ := r + 1 / 2
  have hp : 1 < p := by dsimp [p]; linarith
  let f : ℝ → ℝ := fun x => x ^ (-p)
  have hanti : AntitoneOn f (Set.Ici 1) := by
    intro x hx y hy hxy
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
    exact Real.rpow_le_rpow_of_nonpos hxpos hxy (by dsimp [p]; linarith)
  have hint : IntegrableOn f (Set.Ioi 1) := by
    change IntegrableOn (fun x : ℝ => x ^ (-p)) (Set.Ioi 1)
    exact integrableOn_Ioi_rpow_of_lt (by linarith [hp]) (by norm_num)
  have hnonneg : ∀ x ∈ Set.Ioi (1 : ℝ), 0 ≤ f x := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans (by norm_num) (le_of_lt hx)
    exact Real.rpow_nonneg hx0 _
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := f) 1
    (by simpa only [Nat.cast_one] using hanti)
    (by simpa only [Nat.cast_one] using hint)
    (by simpa only [Nat.cast_one] using hnonneg)
  have hintegral : (∫ x in Set.Ioi ((1 : ℕ) : ℝ), f x) = 1 / (p - 1) := by
    simp only [Nat.cast_one, f]
    rw [integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
    rw [Real.one_rpow, show -p + 1 = -(p - 1) by ring]
    simp only [div_neg, neg_div, neg_neg]
  rw [hintegral] at htail
  have hsum := endpointInversePSeries_summable r hrHalf
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hfirst : (((0 + 1 : ℕ) : ℝ) ^ (-(r + 1 / 2))) = 1 := by norm_num
  have htail' : (∑' k : ℕ, (((k + 2 : ℕ) : ℝ) ^ (-(r + 1 / 2)))) ≤
      1 / (p - 1) := by
    convert htail using 1
  have hbound : (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(r + 1 / 2)))) ≤
      1 + 1 / (p - 1) := by
    have hsplit' : (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(r + 1 / 2)))) =
        1 + ∑' k : ℕ, (((k + 2 : ℕ) : ℝ) ^ (-(r + 1 / 2))) := by
      simpa [Finset.sum_range_one, hfirst, Nat.cast_add, add_assoc] using hsplit.symm
    rw [hsplit']
    simpa only [add_comm] using add_le_add_left htail' 1
  convert hbound using 1 <;> dsimp [endpointInverseHSBound, p] <;> ring

/-- The exact squared Hilbert–Schmidt mass is at most the reviewed
`(1 + 1/(r−1/2))²`, including the source exponents `3/4` and `7/8`. -/
theorem endpointInverseHSSquare_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) :
    endpointInverseHSSquare r ≤ endpointInverseHSBound r ^ 2 := by
  have hB : 0 ≤ endpointInverseHSBound r := by
    unfold endpointInverseHSBound
    have : 0 < r - 1 / 2 := by linarith
    positivity
  have hp := endpointInversePSeries_summable r hrHalf
  have hcol := summable_endpointInverseHSColumn r hrHalf
  have hterm : ∀ k : ℕ, endpointInverseHSColumn r k ≤
      endpointInverseHSBound r * (((k + 1 : ℕ) : ℝ) ^ (-(r + 1 / 2))) :=
    endpointInverseHSColumn_le_pseries r hrHalf
  have htsum := Summable.tsum_le_tsum hterm hcol (hp.mul_left _)
  calc
    endpointInverseHSSquare r ≤
        ∑' k : ℕ, endpointInverseHSBound r *
          (((k + 1 : ℕ) : ℝ) ^ (-(r + 1 / 2))) := htsum
    _ = endpointInverseHSBound r *
        ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ (-(r + 1 / 2))) := by
      rw [tsum_mul_left]
    _ ≤ endpointInverseHSBound r * endpointInverseHSBound r := by
      exact mul_le_mul_of_nonneg_left
        (endpointInversePSeries_tsum_le r hrHalf) hB
    _ = endpointInverseHSBound r ^ 2 := by ring

#assert_trust kernel summable_endpointInverseHSColumn
#assert_trust kernel endpointInverseHSSquare_le
#print axioms endpointInverseHSSquare_le

end NLA.Proofs.SP14
