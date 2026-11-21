import SymmetricMaximizer

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace MF13Verification

/-- The real matrix space in the catalog's order-six question. -/
abbrev Matrix6 := Matrix (Fin 6) (Fin 6) ℝ

/-- The Frobenius norm used below is the trace formula in the catalog. -/
theorem frobenius_norm_eq_sqrt_trace (X : Matrix6) :
    ‖X‖ = Real.sqrt (Matrix.trace (Xᵀ * X)) := by
  have htrace : Matrix.trace (Xᵀ * X) = ∑ i, ∑ j, (X j i) ^ 2 := by
    simp [Matrix.trace, Matrix.mul_apply, pow_two]
  have hnorm := SymmetricMaximizer.frobenius_norm_sq_eq_sum X
  simp only [Real.norm_eq_abs, sq_abs] at hnorm
  rw [htrace, Finset.sum_comm, ← hnorm, Real.sqrt_sq (norm_nonneg X)]

/-- Values of the objective on all Frobenius-unit matrices. -/
def unrestrictedValues (A : Matrix6) : Set ℝ :=
  {r | ∃ X : Matrix6, ‖X‖ = 1 ∧ ‖A * X + X * Aᵀ‖ = r}

/-- Values of the same objective on symmetric Frobenius-unit matrices. -/
def symmetricValues (A : Matrix6) : Set ℝ :=
  {r | ∃ X : Matrix6, Xᵀ = X ∧ ‖X‖ = 1 ∧ ‖A * X + X * Aᵀ‖ = r}

/-- Both maxima in MF-13 exist and have a common value for every real A. -/
theorem common_maximum (A : Matrix6) :
    ∃ r : ℝ, IsGreatest (unrestrictedValues A) r ∧ IsGreatest (symmetricValues A) r := by
  obtain ⟨S, hSymm, hUnit, hAttains⟩ :=
    (SymmetricMaximizer.symmetric_maximizers_all_orders 6 (by decide)).2 (by decide) A
  have bound (X : Matrix6) (hX : ‖X‖ = 1) :
      ‖A * X + X * Aᵀ‖ ≤ ‖A * S + S * Aᵀ‖ := by
    have h := (SymmetricMaximizer.lyapunovOperator A).le_opNorm X
    change ‖SymmetricMaximizer.lyapunov A X‖ ≤
      (SymmetricMaximizer.lyapunovOperator A).opNorm * ‖X‖ at h
    rw [hX, mul_one, ← hAttains] at h
    exact h
  refine ⟨_, ⟨⟨S, hUnit, rfl⟩, ?_⟩, ⟨⟨S, hSymm, hUnit, rfl⟩, ?_⟩⟩
  · rintro _ ⟨X, hX, rfl⟩
    exact bound X hX
  · rintro _ ⟨X, _, hX, rfl⟩
    exact bound X hX

/-- The two maxima in the original MF-13 statement are equal. -/
theorem equal_maxima (A : Matrix6) :
    sSup (unrestrictedValues A) = sSup (symmetricValues A) := by
  obtain ⟨_, hAll, hSymm⟩ := common_maximum A
  exact hAll.csSup_eq.trans hSymm.csSup_eq.symm

end MF13Verification

open Lean Elab Command

run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let targets := #[`MF13Verification.frobenius_norm_eq_sqrt_trace, `MF13Verification.common_maximum,
    `MF13Verification.equal_maxima, `SymmetricMaximizer.all_orders,
    `SymmetricMaximizer.symmetric_maximizers_all_orders,
    `SymmetricMaximizer.exists_integer_counterexample]
  for target in targets do
    for ax in ← collectAxioms target do
      unless allowed.contains ax do
        throwError "{target} depends on an unexpected axiom {ax}"
  logInfo m!"Checked the transitive axioms of {targets.size} declarations."

#print axioms MF13Verification.frobenius_norm_eq_sqrt_trace
#print axioms MF13Verification.common_maximum
#print axioms MF13Verification.equal_maxima
#print axioms SymmetricMaximizer.all_orders
#print axioms SymmetricMaximizer.symmetric_maximizers_all_orders
#print axioms SymmetricMaximizer.exists_integer_counterexample
