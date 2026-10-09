import NLA.TR07.FiniteVector

/-! Finite Markov paths, recording the post-transition states. -/
noncomputable section
open scoped BigOperators
namespace NLA.TR07.Law
variable {α : Type*} [Fintype α]

/-- `paths K L x` records the next `L` states of the finite kernel `K`, starting from `x`. -/
def paths (K : α → Law α) : (L : ℕ) → α → Law (Fin L → α)
  | 0, _ => Law.pure Fin.elim0
  | L+1, x => (K x).bind (fun y => (paths K L y).map (fun z => Fin.cons y z))

theorem expect_paths_zero (K : α → Law α) (x : α) (f : (Fin 0 → α) → ℝ) :
    (paths K 0 x).expect f = f Fin.elim0 := by simp [paths]

theorem expect_paths_succ (K : α → Law α) (L : ℕ) (x : α)
    (f : (Fin (L+1) → α) → ℝ) :
    (paths K (L+1) x).expect f =
      (K x).expect (fun y => (paths K L y).expect (fun z => f (Fin.cons y z))) := by
  simp [paths, expect_bind]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mean_paths_succ (K : α → Law α) (L : ℕ) (x : α)
    (f : (Fin (L+1) → α) → E) :
    (paths K (L+1) x).mean f =
      (K x).mean (fun y => (paths K L y).mean (fun z => f (Fin.cons y z))) := by
  simp [paths, mean_bind, mean_map]

/-- The mean at path position `j` is the `(j+1)`st iterate of the one-step mean map. -/
theorem mean_paths_coordinate (K : α → Law α) (u : α → E) (T : E →ₗ[ℝ] E)
    (hmean : ∀ x, (K x).mean u = T (u x))
    (L : ℕ) (x : α) (j : Fin L) :
    (paths K L x).mean (fun z => u (z j)) = (T^(j.val+1)) (u x) := by
  induction L generalizing x with
  | zero => exact Fin.elim0 j
  | succ L ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [mean_paths_succ]
      simp only [Fin.cons_zero, mean_const, Fin.val_zero, zero_add, pow_one]
      exact hmean x
    · rw [mean_paths_succ]
      simp only [Fin.cons_succ]
      simp_rw [ih]
      rw [mean_linear, hmean]
      simp only [Fin.val_succ, pow_succ, Module.End.mul_apply]

end NLA.TR07.Law
