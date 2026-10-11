import NLA.Proofs.RA06.GraphPower

/-! A uniform ordinary-sensitivity upper bound from two complete-graph stars. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA06

/-- Averaging the two-leg inequality over every third vertex bounds one
complete-graph edge by two star energies. -/
theorem pairPower_le_complete
    {v : ℕ} (p : ℝ) (hp : 1 ≤ p)
    (z : Fin v → ℝ) (i j : Fin v) :
    (v : ℝ) * Real.rpow |z i - z j| p ≤
      (2 * Real.rpow 2 (p - 1)) * CompleteEnergy p z := by
  let a : ℝ := Real.rpow |z i - z j| p
  let B : ℝ := Real.rpow 2 (p - 1)
  have hpoint (k : Fin v) :
      a ≤ B * (Real.rpow |z i - z k| p + Real.rpow |z j - z k| p) :=
    abs_sub_rpow_le_two_legs p (z i) (z j) (z k) hp
  have hsum : (∑ k : Fin v, a) ≤
      ∑ k : Fin v,
        B * (Real.rpow |z i - z k| p + Real.rpow |z j - z k| p) := by
    apply Finset.sum_le_sum
    intro k _
    exact hpoint k
  have hi := sum_differences_le_complete p (by linarith : 0 < p) z i
  have hj := sum_differences_le_complete p (by linarith : 0 < p) z j
  have hB : 0 ≤ B := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
  have hleft : (∑ k : Fin v, a) = (v : ℝ) * a := by
    simp
  have hright :
      (∑ k : Fin v,
        B * (Real.rpow |z i - z k| p + Real.rpow |z j - z k| p)) =
      B * ((∑ k : Fin v, Real.rpow |z i - z k| p) +
        (∑ k : Fin v, Real.rpow |z j - z k| p)) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hsum' : (v : ℝ) * a ≤
      B * ((∑ k : Fin v, Real.rpow |z i - z k| p) +
        (∑ k : Fin v, Real.rpow |z j - z k| p)) := by
    calc
      (v : ℝ) * a = ∑ k : Fin v, a := hleft.symm
      _ ≤ ∑ k : Fin v,
          B * (Real.rpow |z i - z k| p + Real.rpow |z j - z k| p) := hsum
      _ = _ := hright
  calc
    (v : ℝ) * Real.rpow |z i - z j| p = (v : ℝ) * a := rfl
    _ ≤ B * ((∑ k : Fin v, Real.rpow |z i - z k| p) +
        (∑ k : Fin v, Real.rpow |z j - z k| p)) := hsum'
    _ ≤ B * (CompleteEnergy p z + CompleteEnergy p z) :=
      mul_le_mul_of_nonneg_left (add_le_add hi hj) hB
    _ = (2 * Real.rpow 2 (p - 1)) * CompleteEnergy p z := by dsimp [B]; ring

#print axioms pairPower_le_complete

end NLA.Proofs.RA06
