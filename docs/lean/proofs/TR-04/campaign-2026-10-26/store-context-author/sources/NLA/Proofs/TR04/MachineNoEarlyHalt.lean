import NLA.Proofs.TR04.MachineRelocation

/-! A running endpoint of an actual ordinary instruction path certifies that
no earlier halt or failure was crossed. No termination assumption is added. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem ordinaryStep_eq_of_stopped {P : Program} {s : State P}
    (hs : s.status ≠ .running) : ordinaryStep P s = s := by
  cases h : s.status with
  | running => exact False.elim (hs h)
  | halted base => simp [ordinaryStep,h]
  | failed => simp [ordinaryStep,h]

theorem ordinary_iterate_eq_of_stopped {P : Program} {s : State P}
    (hs : s.status ≠ .running) (n : ℕ) : (ordinaryStep P)^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,ordinaryStep_eq_of_stopped hs]

theorem ordinary_running_prefix {P : Program} (s : State P) (n : ℕ)
    (hn : ((ordinaryStep P)^[n] s).status = .running) (k : ℕ) (hk : k ≤ n) :
    ((ordinaryStep P)^[k] s).status = .running := by
  by_contra hs
  have heq : (ordinaryStep P)^[n] s = (ordinaryStep P)^[k] s := by
    have hnk : n = (n-k)+k := by omega
    rw [hnk,Function.iterate_add_apply,ordinary_iterate_eq_of_stopped hs]
  rw [heq] at hn
  exact hs hn

theorem ordinary_nohalt_prefix_of_running {P : Program} (s : State P) (n : ℕ)
    (hn : ((ordinaryStep P)^[n] s).status = .running) (k : ℕ) (hk : k < n) :
    instructionIsHalt (P.code ((ordinaryStep P)^[k] s).label) = false := by
  have hs := ordinary_running_prefix s n hn k hk.le
  have hsnext := ordinary_running_prefix s n hn (k+1) (by omega)
  rw [Function.iterate_succ_apply'] at hsnext
  cases hi : P.code ((ordinaryStep P)^[k] s).label <;>
    simp only [instructionIsHalt]
  simp [ordinaryStep,hs,hi] at hsnext

#assert_trust kernel ordinaryStep_eq_of_stopped
#assert_trust kernel ordinary_iterate_eq_of_stopped
#assert_trust kernel ordinary_running_prefix
#assert_trust kernel ordinary_nohalt_prefix_of_running
#print axioms ordinary_nohalt_prefix_of_running
end NLA.Proofs.TR04
