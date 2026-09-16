/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The n² Gaussian probabilities are multiplied symbolically using the actual
nested product measure. All powers and the final probability exponent are
exact; no sample probability or high-dimensional integration is substituted.
-/
import NLA.IE04.GaussianDensity
import NLA.IE04.Scalars
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section
namespace NLA.IE04

theorem gaussianBox_eq_pi (n : ℕ) :
    gaussianBox n = Set.univ.pi (fun i : Fin n => Set.univ.pi (fun j : Fin n =>
      Set.Icc (witnessMatrix n i j - (1 : Mat n) i j - boxRadius n)
        (witnessMatrix n i j - (1 : Mat n) i j + boxRadius n))) := by
  ext G
  constructor
  · intro h i hi j hj
    have hij := abs_le.mp (h i j)
    constructor <;> linarith
  · intro h i j
    rw [abs_le]
    have hij := h i (Set.mem_univ i) j (Set.mem_univ j)
    constructor <;> linarith [hij.1, hij.2]

theorem gaussian_box_product (n : ℕ) :
    MeasurableSet (gaussianBox n) ∧
      gaussianMatrix n (gaussianBox n) =
        ∏ i : Fin n, ∏ j : Fin n,
          gaussianReal 0 1 (Set.Icc
            (witnessMatrix n i j - (1 : Mat n) i j - boxRadius n)
            (witnessMatrix n i j - (1 : Mat n) i j + boxRadius n)) := by
  rw [gaussianBox_eq_pi]
  refine ⟨MeasurableSet.univ_pi (fun _ => MeasurableSet.univ_pi
    (fun _ => measurableSet_Icc)), ?_⟩
  let intervals : Fin n → Fin n → Set ℝ := fun i j =>
    Set.Icc (witnessMatrix n i j - (1 : Mat n) i j - boxRadius n)
      (witnessMatrix n i j - (1 : Mat n) i j + boxRadius n)
  have houter := Measure.pi_pi
    (fun _ : Fin n => Measure.pi (fun _ : Fin n => gaussianReal 0 1))
    (fun i : Fin n => Set.univ.pi (intervals i))
  have hinner : (∏ i : Fin n, (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (Set.univ.pi (intervals i))) =
      ∏ i : Fin n, ∏ j : Fin n, gaussianReal 0 1 (intervals i j) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact Measure.pi_pi (fun _ : Fin n => gaussianReal 0 1) (intervals i)
  exact houter.trans hinner

theorem witness_gaussian_center_bound {n : ℕ} (i j : Fin n) :
    |witnessMatrix n i j - (1 : Mat n) i j| ≤ 1 := by
  simp only [witnessMatrix, Matrix.one_apply]
  split_ifs <;> norm_num

theorem interval_factor_exact (n : ℕ) :
    boxRadius n / 16 = 1 / (2 : ℝ) ^ (n ^ 2 + n + 5) := by
  have hpow : (2 : ℝ) ^ (n ^ 2 + n + 5) =
      (2 : ℝ) ^ (n ^ 2 + n + 1) * 16 := by
    rw [show n ^ 2 + n + 5 = (n ^ 2 + n + 1) + 4 by omega,
      pow_add (2 : ℝ) (n ^ 2 + n + 1) 4]
    norm_num
  simp only [boxRadius, div_div, hpow]

theorem product_lower_factor_exact (n : ℕ) :
    ENNReal.ofReal (1 / (2 : ℝ) ^ probabilityExponent n) =
      ∏ _i : Fin n, ∏ _j : Fin n, ENNReal.ofReal (boxRadius n / 16) := by
  have hnonneg : 0 ≤ boxRadius n / 16 := by unfold boxRadius; positivity
  have hexponent : (n ^ 2 + n + 5) * (n * n) = probabilityExponent n := by
    unfold probabilityExponent
    ring
  calc
    ENNReal.ofReal (1 / (2 : ℝ) ^ probabilityExponent n) =
        ENNReal.ofReal ((boxRadius n / 16) ^ (n * n)) := by
      rw [interval_factor_exact, div_pow, one_pow, ← pow_mul, hexponent]
    _ = ENNReal.ofReal (boxRadius n / 16) ^ (n * n) :=
      ENNReal.ofReal_pow hnonneg _
    _ = ∏ _i : Fin n, ∏ _j : Fin n, ENNReal.ofReal (boxRadius n / 16) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

theorem gaussian_box_probability {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal (1 / (2 : ℝ) ^ probabilityExponent n) ≤
      gaussianMatrix n (gaussianBox n) := by
  rw [(gaussian_box_product n).2, product_lower_factor_exact]
  apply Finset.prod_le_prod'
  intro i hi
  apply Finset.prod_le_prod'
  intro j hj
  exact gaussian_interval_lower _ _ (witness_gaussian_center_bound i j)
    (scalar_budgets hn).1 (scalar_budgets hn).2.1

#assert_trust kernel gaussian_box_product
#print axioms gaussian_box_product
#assert_trust kernel gaussian_box_probability
#print axioms gaussian_box_probability

end NLA.IE04
