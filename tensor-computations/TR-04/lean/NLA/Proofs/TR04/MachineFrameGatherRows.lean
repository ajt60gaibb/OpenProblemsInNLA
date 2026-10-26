import NLA.Proofs.TR04.MachineFrameGatherExecution

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem frameGatherProgram_inner_iterations (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (i selected address : ℕ) (value : ℝ) (hi : i < P.rows)
    (k : ℕ) (hk : k ≤ P.width) :
    ∃ a b : ℕ, ∃ v : ℝ, (ordinaryStep frameGatherProgram)^[11 * k]
      (frameGatherInnerState memory P i 0 selected address value) =
        frameGatherInnerState memory P i k a b v := by
  induction k with
  | zero => exact ⟨selected, address, value, rfl⟩
  | succ k ih =>
    obtain ⟨a, b, v, hv⟩ := ih (by omega)
    refine ⟨P.column k, P.sourceAddress (i * P.width + k),
      memory (P.sourceAddress (i * P.width + k)), ?_⟩
    rw [Nat.mul_succ, Nat.add_comm (11 * k) 11, Function.iterate_add_apply, hv]
    exact frameGatherProgram_eleven_steps memory P hP hd i k a b v hi (by omega)

set_option maxHeartbeats 1200000 in
theorem frameGatherProgram_row_exit (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (i selected address : ℕ) (value : ℝ) :
    (ordinaryStep frameGatherProgram)^[2]
      (frameGatherInnerState memory P i P.width selected address value) =
        frameGatherOuterState memory P (i + 1)
          ![P.width, P.counter P.width, P.inputBase + i * P.rows, selected, address] value := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Function.iterate_succ_apply', ordinaryStep,
    frameGatherProgram, frameGatherInnerState, frameGatherOuterState, Nat.add_mul]
  all_goals try rfl
  funext r
  fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff]

theorem frameGatherProgram_one_row (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (i : ℕ) (hi : i < P.rows) (aux : Fin 5 → ℕ) (value : ℝ) :
    ∃ aux' : Fin 5 → ℕ, ∃ v : ℝ,
      (ordinaryStep frameGatherProgram)^[11 * P.width + 7]
        (frameGatherOuterState memory P i aux value) = frameGatherOuterState memory P (i + 1) aux' v := by
  obtain ⟨a, b, v, hv⟩ := frameGatherProgram_inner_iterations memory P hP hd
    i (aux 3) (aux 4) value hi P.width le_rfl
  refine ⟨![P.width, P.counter P.width, P.inputBase + i * P.rows, a, b], v, ?_⟩
  have hsetup := frameGatherProgram_row_setup memory P hP i hi aux value
  have hbody : (ordinaryStep frameGatherProgram)^[11 * P.width + 5]
      (frameGatherOuterState memory P i aux value) = frameGatherInnerState memory P i P.width a b v := by
    rw [Function.iterate_add_apply, hsetup, hv]
  rw [show 11 * P.width + 7 = 2 + (11 * P.width + 5) by omega,
    Function.iterate_add_apply, hbody]
  exact frameGatherProgram_row_exit memory P i a b v

theorem frameGatherProgram_rows (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (aux : Fin 5 → ℕ) (value : ℝ) (i : ℕ) (hi : i ≤ P.rows) :
    ∃ aux' : Fin 5 → ℕ, ∃ v : ℝ,
      (ordinaryStep frameGatherProgram)^[i * (11 * P.width + 7)]
        (frameGatherOuterState memory P 0 aux value) = frameGatherOuterState memory P i aux' v := by
  induction i with
  | zero => exact ⟨aux, value, by simp⟩
  | succ i ih =>
    obtain ⟨aux', v, hv⟩ := ih (by omega)
    obtain ⟨aux'', v', hv'⟩ := frameGatherProgram_one_row memory P hP hd i (by omega) aux' v
    refine ⟨aux'', v', ?_⟩
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (i * (11 * P.width + 7)) (11 * P.width + 7),
      Function.iterate_add_apply, hv]
    exact hv'

#assert_trust kernel frameGatherProgram_inner_iterations
#assert_trust kernel frameGatherProgram_row_exit
#assert_trust kernel frameGatherProgram_one_row
#assert_trust kernel frameGatherProgram_rows
#print axioms frameGatherProgram_rows
end NLA.Proofs.TR04
