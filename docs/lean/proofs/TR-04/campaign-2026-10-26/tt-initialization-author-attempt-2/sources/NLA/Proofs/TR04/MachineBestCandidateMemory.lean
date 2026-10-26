import NLA.Proofs.TR04.MachineSquaredErrorTrace

/-! Actual read-only candidate arrays and the finite minimum invariant. No
candidate, error, or minimizing index is placed in the input as an oracle. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04

structure BestCandidateData where
  count : ℕ
  entries : ℕ
  baseA : ℕ
  store : ℕ
  memory : ℕ → ℝ

def BestCandidateData.candidateBase (p : BestCandidateData) (j : ℕ) : ℕ :=
  p.store + j * p.entries

def BestCandidateData.candidateError (p : BestCandidateData) (j : ℕ) : ℝ :=
  squaredErrorSum p.memory p.baseA (p.candidateBase j) p.entries

def BestCandidateData.MinimumSoFar (p : BestCandidateData) (j winner : ℕ) (value : ℝ) : Prop :=
  j = 0 ∨ winner < j ∧ value = p.candidateError winner ∧
    ∀ i < j, value ≤ p.candidateError i

theorem BestCandidateData.minimum_take (p : BestCandidateData) (j winner : ℕ) (value : ℝ)
    (h : p.MinimumSoFar j winner value) (ht : j = 0 ∨ p.candidateError j < value) :
    p.MinimumSoFar (j + 1) j (p.candidateError j) := by
  right
  refine ⟨by omega, rfl, ?_⟩
  intro i hi
  by_cases hij : i = j
  · subst i
    exact le_rfl
  · have hi' : i < j := by omega
    have hj : j ≠ 0 := by omega
    obtain ⟨_, _, hmin⟩ := h.resolve_left hj
    have hlt := ht.resolve_left hj
    exact hlt.le.trans (hmin i hi')

theorem BestCandidateData.minimum_keep (p : BestCandidateData) (j winner : ℕ) (value : ℝ)
    (h : p.MinimumSoFar j winner value) (hj : j ≠ 0) (ht : ¬ p.candidateError j < value) :
    p.MinimumSoFar (j + 1) winner value := by
  obtain ⟨hw, he, hmin⟩ := h.resolve_left hj
  right
  refine ⟨by omega, he, ?_⟩
  intro i hi
  by_cases hij : i = j
  · subst i
    exact le_of_not_gt ht
  · exact hmin i (by omega)

#assert_trust kernel BestCandidateData.minimum_take
#assert_trust kernel BestCandidateData.minimum_keep
#print axioms BestCandidateData.minimum_take
#print axioms BestCandidateData.minimum_keep
end NLA.Proofs.TR04
