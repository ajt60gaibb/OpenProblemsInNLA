import NLA.Proofs.PF05.Operator

/-! The actual coordinate operator of a first-order trace-preserving direction.
The right coordinates retain the off-diagonal trace weight two. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.PF05
open NLA.Statements.PF05

/-- A full-rank rectangular product has exactly one infinitesimal change of
basis. This is an algebraic consequence of the actual first-order equation. -/
theorem full_rank_infinitesimal_operator {p q : ℕ}
    (X E : Matrix (Fin p) (Fin 3) ℝ)
    (Y F : Matrix (Fin 3) (Fin q) ℝ)
    (hfirst : E * Y + X * F = 0)
    (hX : Submodule.span ℝ (Set.range X.row) = ⊤)
    (hY : Submodule.span ℝ (Set.range Y.col) = ⊤) :
    ∃! T : Matrix (Fin 3) (Fin 3) ℝ,
      E = X * T ∧ F = -(T * Y) := by
  obtain ⟨U, hUX⟩ := left_inverse_of_row_span X hX
  obtain ⟨V, hYV⟩ := right_inverse_of_column_span Y hY
  let T : Matrix (Fin 3) (Fin 3) ℝ := -(F * V)
  have hE : E = X * T := by
    have heq := congrArg (fun Z => Z * V) hfirst
    have hsum : E + X * (F * V) = 0 := by
      simpa [Matrix.add_mul, Matrix.mul_assoc, hYV] using heq
    simpa [T] using (eq_neg_of_add_eq_zero_left hsum)
  have hF : F = -(T * Y) := by
    have heq := congrArg (fun Z => U * Z) hfirst
    have hsum : T * Y + F = 0 := by
      simpa [Matrix.mul_add, hE, ← Matrix.mul_assoc, hUX] using heq
    exact eq_neg_of_add_eq_zero_right hsum
  refine ⟨T, ⟨hE, hF⟩, ?_⟩
  intro T' hT'
  have heq : X * T' = X * T := hT'.1.symm.trans hE
  have heq' := congrArg (fun Z => U * Z) heq
  simpa [← Matrix.mul_assoc, hUX] using heq'

/-- The literal trace derivatives, expressed in the actual weighted coordinates. -/
theorem first_order_coordinates {p q : ℕ}
    (A E : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B F : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i, Symmetric (A i)) (hE : ∀ i, Symmetric (E i))
    (hB : ∀ j, Symmetric (B j)) (hF : ∀ j, Symmetric (F j))
    (hfirst : ∀ i j, Matrix.trace (E i * B j) + Matrix.trace (A i * F j) = 0) :
    leftCoordinates E * rightCoordinates B +
      leftCoordinates A * rightCoordinates F = 0 := by
  ext i j
  have h := hfirst i j
  rw [trace_mul_symmetric_coordinates _ _ (hE i) (hB j),
    trace_mul_symmetric_coordinates _ _ (hA i) (hF j)] at h
  simp [leftCoordinates, rightCoordinates, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.add_apply]
  nlinarith [h]

/-- Every actual feasible direction of a rank-three size-two factorization
has a unique primal coordinate operator and its negative trace-dual operator. -/
theorem feasible_direction_operator {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A E : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B F : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (hfact : Factorization M A B) (hrank : M.rank = 3)
    (hdir : FeasibleDirection A E B F) :
    ∃! T : Matrix (Fin 3) (Fin 3) ℝ,
      leftCoordinates E = leftCoordinates A * T ∧
      rightCoordinates F = -(T * rightCoordinates B) := by
  exact full_rank_infinitesimal_operator _ _ _ _
    (first_order_coordinates A E B F (fun i => (hfact.1 i).1) hdir.1
      (fun j => (hfact.2.1 j).1) hdir.2.1 hdir.2.2.1)
    (factorization_coordinate_spans M A B hfact hrank).1
    (factorization_coordinate_spans M A B hfact hrank).2

#assert_trust kernel full_rank_infinitesimal_operator
#assert_trust kernel first_order_coordinates
#assert_trust kernel feasible_direction_operator
#print axioms feasible_direction_operator

end NLA.Proofs.PF05
