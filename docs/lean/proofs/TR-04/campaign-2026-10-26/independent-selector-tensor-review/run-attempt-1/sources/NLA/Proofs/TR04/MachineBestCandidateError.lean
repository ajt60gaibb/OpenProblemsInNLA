import NLA.Proofs.TR04.MachineBestCandidate

/-! The actual embedded squared-error call, preserving the selector's loop
parameters and retained best error outside its injected register frame. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem bestCandidateProgram_error (p : BestCandidateData) (j winner : ℕ)
    (value : ℝ) (reals : Fin 3 → ℝ) :
    ∃ a b : ℝ, (ordinaryStep bestCandidateProgram)^[9 * p.entries + 2]
      (bestCandidateErrorState p j winner value reals) =
        bestCandidateAfterError p j winner value a b := by
  let E := bestCandidateErrorEmbedding
  have hs := bestCandidate_error_relates p j winner value reals
  have hn := squaredErrorProgram_nohalt_prefix p.memory p.baseA (p.candidateBase j) p.entries
    (reals 0) (reals 1) (reals 2)
  have hr := E.ordinary_iterate_relates hs (9 * p.entries + 2) hn
  obtain ⟨a, b, he⟩ := squaredErrorProgram_return p.memory p.baseA (p.candidateBase j) p.entries
    (reals 0) (reals 1) (reals 2)
  rw [he] at hr
  have hnat : ∀ r : Fin 13, r.val < 8 →
      ((ordinaryStep bestCandidateProgram)^[9 * p.entries + 2]
        (bestCandidateErrorState p j winner value reals)).natural r =
          (bestCandidateErrorState p j winner value reals).natural r := by
    intro r hsmall
    apply E.ordinary_iterate_natural_outside hs _ hn
    intro i hri
    have hv := congrArg (fun x : Fin 13 => x.val) hri
    change r.val = 8 + i.val at hv
    omega
  have hbest := E.ordinary_iterate_real_outside hs (9 * p.entries + 2) hn
    (⟨3, by decide⟩ : Fin 4) (by
      intro i hri
      have hv := congrArg (fun x : Fin 4 => x.val) hri
      change 3 = i.val at hv
      have hi : i.val < 3 := i.isLt
      omega)
  have ha : E.Relates (squaredErrorReturnState p.memory p.baseA (p.candidateBase j)
      p.entries a b) (bestCandidateAfterError p j winner value a b) := by
    constructor
    · rfl
    · funext r
      fin_cases r <;> rfl
    · funext r
      fin_cases r <;> rfl
    · rfl
    · rfl
  refine ⟨a, b, ?_⟩
  apply machineState_ext
  · exact hr.label.trans ha.label.symm
  · funext r
    by_cases hsmall : r.val < 3
    · let i : Fin 3 := ⟨r.val, hsmall⟩
      have heq : E.reals i = r := Fin.ext rfl
      rw [← heq]
      exact (hr.real_apply i).trans (ha.real_apply i).symm
    · have heq : r = (⟨3, by decide⟩ : Fin 4) := by
        apply Fin.ext
        have hh : r.val < 4 := r.isLt
        change r.val = 3
        omega
      rw [heq]
      exact hbest
  · funext r
    by_cases hsmall : r.val < 8
    · have hh := hnat r hsmall
      simpa only [bestCandidateErrorState, bestCandidateAfterError, bestCandidateState,
        dif_pos hsmall] using hh
    · let i : Fin 5 := ⟨r.val - 8, by have hh : r.val < 13 := r.isLt; omega⟩
      have heq : E.naturals i = r := by
        apply Fin.ext
        change 8 + (r.val - 8) = r.val
        omega
      rw [← heq]
      exact (hr.natural_apply i).trans (ha.natural_apply i).symm
  · exact hr.memory.trans ha.memory.symm
  · exact hr.status.trans ha.status.symm

#assert_trust kernel bestCandidateProgram_error
#print axioms bestCandidateProgram_error
end NLA.Proofs.TR04
