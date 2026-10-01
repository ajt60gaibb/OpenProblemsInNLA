import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Energy control for the inverse-square perturbed oscillator

The transformed scalar Bessel equation has the form
`v'' + v = 3 v / (4 r²)`. Its energy times `exp(3/(4r))` decreases on
`[1,∞)`. This argument includes zero energy and never divides by it.
-/

noncomputable section

open Set

namespace ProofProject

def oscillatorWeightedEnergy (v p : ℝ → ℝ) (r : ℝ) : ℝ :=
  (v r ^ 2 + p r ^ 2) * Real.exp (3 / (4 * r))

theorem oscillatorWeightedEnergy_hasDerivAt {v p : ℝ → ℝ} {r : ℝ}
    (hr : r ≠ 0) (hv : HasDerivAt v (p r) r)
    (hp : HasDerivAt p (-v r + 3 * v r / (4 * r ^ 2)) r) :
    HasDerivAt (oscillatorWeightedEnergy v p)
      (-(3 / (4 * r ^ 2)) * (v r - p r) ^ 2 * Real.exp (3 / (4 * r))) r := by
  have hd := ((hv.pow 2).add (hp.pow 2)).mul
    ((hasDerivAt_const r (3 : ℝ)).div ((hasDerivAt_id r).const_mul 4)
      (by exact mul_ne_zero (by norm_num) hr)).exp
  convert! hd using 1
  dsimp
  field_simp
  ring

/-- The exact integrating factor gives monotonicity without a Gronwall theorem. -/
theorem oscillatorWeightedEnergy_antitoneOn {v p : ℝ → ℝ}
    (hv : ∀ r, 1 ≤ r → HasDerivAt v (p r) r)
    (hp : ∀ r, 1 ≤ r → HasDerivAt p (-v r + 3 * v r / (4 * r ^ 2)) r) :
    AntitoneOn (oscillatorWeightedEnergy v p) (Ici 1) := by
  have hd (r : ℝ) (hr : 1 ≤ r) := oscillatorWeightedEnergy_hasDerivAt
    (show r ≠ 0 by linarith) (hv r hr) (hp r hr)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (1 : ℝ))
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt)
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one (interior_subset hr)
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _))
    (Real.exp_pos _).le

/-- A uniform energy bound for every radius at least one. -/
theorem oscillator_energy_le {v p : ℝ → ℝ}
    (hv : ∀ r, 1 ≤ r → HasDerivAt v (p r) r)
    (hp : ∀ r, 1 ≤ r → HasDerivAt p (-v r + 3 * v r / (4 * r ^ 2)) r)
    {r : ℝ} (hr : 1 ≤ r) :
    v r ^ 2 + p r ^ 2 ≤ (v 1 ^ 2 + p 1 ^ 2) * Real.exp (3 / 4) := by
  have h := oscillatorWeightedEnergy_antitoneOn hv hp (by norm_num : (1 : ℝ) ∈ Ici (1 : ℝ))
    hr hr
  have he : 1 ≤ Real.exp (3 / (4 * r)) := Real.one_le_exp (by positivity)
  calc
    _ ≤ (v r ^ 2 + p r ^ 2) * Real.exp (3 / (4 * r)) :=
      le_mul_of_one_le_right (add_nonneg (sq_nonneg _) (sq_nonneg _)) he
    _ ≤ _ := by simpa only [oscillatorWeightedEnergy, mul_one] using h

/-- Both components have one finite uniform bound, also when the initial
energy is zero. -/
theorem exists_oscillator_uniform_bound {v p : ℝ → ℝ}
    (hv : ∀ r, 1 ≤ r → HasDerivAt v (p r) r)
    (hp : ∀ r, 1 ≤ r → HasDerivAt p (-v r + 3 * v r / (4 * r ^ 2)) r) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ r, 1 ≤ r → |v r| ≤ V ∧ |p r| ≤ V := by
  let E := (v 1 ^ 2 + p 1 ^ 2) * Real.exp (3 / 4)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨Real.sqrt E, Real.sqrt_nonneg _, ?_⟩
  intro r hr
  have h := oscillator_energy_le hv hp hr
  have hs := Real.sq_sqrt hE
  have hv0 := abs_nonneg (v r)
  have hp0 := abs_nonneg (p r)
  have hV := Real.sqrt_nonneg E
  change v r ^ 2 + p r ^ 2 ≤ E at h
  constructor <;> nlinarith [sq_abs (v r), sq_abs (p r), sq_nonneg (v r), sq_nonneg (p r)]

end ProofProject
