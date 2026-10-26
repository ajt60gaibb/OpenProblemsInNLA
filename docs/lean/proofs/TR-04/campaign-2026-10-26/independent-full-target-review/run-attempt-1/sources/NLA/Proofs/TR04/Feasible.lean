import NLA.Proofs.TR04.Reshape

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.TR04
open NLA.Computation.TensorTrainApproximation
open Set

/-- The zero tensor is feasible even when some requested rank is zero. -/
theorem feasible_zero (S : Shape) (r : Ranks S) : Feasible S r 0 := by
  intro j
  simp

theorem feasible_nonempty (S : Shape) (r : Ranks S) :
    {Y : Tensor S | Feasible S r Y}.Nonempty := ⟨0, feasible_zero S r⟩

/-- Closedness of the actual real matrix rank constraint, including empty matrices. -/
theorem isClosed_matrix_rank_le {m n : Type*} [Fintype m] [Fintype n] (r : ℕ) :
    IsClosed {M : Matrix m n ℝ | Matrix.rank M ≤ r} := by
  classical
  let L : Matrix m n ℝ →ₗ[ℝ] ((n → ℝ) →L[ℝ] (m → ℝ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toLin'.toLinearMap
  have hL : Continuous L := L.continuous_of_finiteDimensional
  have hopen := (isOpen_setOfPred_nat_le_rank (𝕜 := ℝ) (E := n → ℝ)
    (F := m → ℝ) (r + 1)).preimage hL
  have heq : L ⁻¹' {f : (n → ℝ) →L[ℝ] (m → ℝ) |
      (r + 1 : ℕ) ≤ (f : (n → ℝ) →ₗ[ℝ] (m → ℝ)).rank} =
      {M : Matrix m n ℝ | Matrix.rank M ≤ r}ᶜ := by
    ext M
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_compl_iff]
    change (↑(r + 1) ≤ Module.rank ℝ (LinearMap.range M.mulVecLin)) ↔ ¬ Matrix.rank M ≤ r
    rw [← Module.finrank_eq_rank]
    simp only [Nat.cast_le, Matrix.rank, Nat.not_le, Nat.add_one_le_iff]
  rw [heq] at hopen
  simpa only [compl_compl] using hopen.isClosed_compl

/-- Every prescribed unfolding rank bound defines a closed tensor set. -/
theorem isClosed_feasible (S : Shape) (r : Ranks S) :
    IsClosed {Y : Tensor S | Feasible S r Y} := by
  have heq : {Y : Tensor S | Feasible S r Y} =
      ⋂ j : Cut S, (fun Y : Tensor S => Unfold S Y j) ⁻¹'
        {M | Matrix.rank M ≤ r j} := by
    ext Y
    simp [Feasible]
  rw [heq]
  exact isClosed_iInter fun j => (isClosed_matrix_rank_le (r j)).preimage (continuous_unfold S j)

#assert_trust kernel feasible_zero
#assert_trust kernel feasible_nonempty
#assert_trust kernel isClosed_matrix_rank_le
#assert_trust kernel isClosed_feasible
#print axioms isClosed_feasible
end NLA.Proofs.TR04
