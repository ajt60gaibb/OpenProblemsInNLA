import NLA.Proofs.SP14.EndpointFiniteInverseLinearity
import NLA.Proofs.SP14.EndpointFiniteInverseTail
import Mathlib.Analysis.Normed.Operator.Extend

/-!
The finite-support weighted coefficients form a dense complex submodule of
the literal Sobolev coefficient Hilbert space. This is the domain for extending
the actual finite triangular inverse into probability-Haar `L²`.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- Weighted vectors with finite coefficient support, with the source's
ordinary one-sided nonnegative index. -/
def endpointFiniteSupport (r : ℝ) : Submodule ℂ (SobolevCoeff r) where
  carrier := {y | ∃ N : ℕ, ∀ n : ℕ, N ≤ n → y n = 0}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro n hn
    simp
  add_mem' := by
    intro y z ⟨M, hM⟩ ⟨N, hN⟩
    refine ⟨max M N, ?_⟩
    intro n hn
    simp [hM n (le_trans (le_max_left M N) hn),
      hN n (le_trans (le_max_right M N) hn)]
  smul_mem' := by
    intro c y ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    simp [hN n hn]

private theorem endpointFiniteSupport_truncation (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    sobolevTruncation r N y ∈ endpointFiniteSupport r := by
  refine ⟨N, ?_⟩
  intro n hn
  rw [sobolevTruncation_apply]
  simp [not_lt.mpr hn]

/-- The literal first-`N` truncations prove density of finite-support vectors;
the empty truncation is included. -/
theorem endpointFiniteSupport_dense (r : ℝ) :
    DenseRange (endpointFiniteSupport r).subtype := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro y
  apply mem_closure_of_tendsto (tendsto_sobolevTruncation r y)
  apply Filter.Eventually.of_forall
  intro N
  exact ⟨⟨sobolevTruncation r N y,
    endpointFiniteSupport_truncation r y N⟩, rfl⟩

#assert_trust kernel endpointFiniteSupport_dense
#print axioms endpointFiniteSupport_dense

end NLA.Proofs.SP14
