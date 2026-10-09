import ProofProject.BasisEnergy
import ProofProject.GrowthRate

/-!
# The geometric estimate required by the upper-bound synthesis argument

The sharp estimate is a proof-side interface, proved with an absolute constant
in `SharpTailGeometry`. Coefficient-tail inequalities allow zero vectors; on
the nonzero subfamily they force linear independence. This avoids deleting
zero input vectors during synthesis.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

def HasSynthesisTailBound (f : Fin n → H) (K : ℝ) : Prop :=
  ∀ (c : Fin n → ℂ) (k : ℕ), ‖synthesisTail f c k‖ ≤ K * ‖finiteSynthesis f c‖

/-- Bounded coefficient tails prevent any cancellation involving a nonzero
coordinate vector in the kernel of synthesis. -/
lemma HasSynthesisTailBound.kernel_coordinate {f : Fin n → H} {K : ℝ}
    (h : HasSynthesisTailBound f K) {c : Fin n → ℂ}
    (hc : finiteSynthesis f c = 0) (j : Fin n) : c j • f j = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hc, norm_zero, mul_zero] using coordinate_bound_of_tail_bound f c K (h c) j

/-- In particular the circle polynomial cannot vanish unless every vector is
zero. This is the positivity needed in the analytic proof of the geometry. -/
lemma HasSynthesisTailBound.synthesis_ne_zero {f : Fin n → H} {K : ℝ}
    (h : HasSynthesisTailBound f K) (hf : ∃ j, f j ≠ 0)
    {c : Fin n → ℂ} (hc : ∀ j, c j ≠ 0) : finiteSynthesis f c ≠ 0 := by
  intro hz
  obtain ⟨j, hj⟩ := hf
  have heq := congrArg norm (h.kernel_coordinate hz j)
  rw [norm_smul, norm_zero] at heq
  exact hj (norm_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left (norm_ne_zero_iff.mpr (hc j))))

/-- The sharp Hilbert geometry assertion, uniform in the bound, dimension,
and Hilbert space in the fixed universe. `SharpTailGeometry` proves this
interface for `C = 16 * exp 2`. Families with zero vectors are included via
coefficient-tail inequalities, the direct extension of the source projection
statement. -/
def HasSharpTailGeometry (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ {K : ℝ}, 1 < K →
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      {n : ℕ} (f : Fin n → H), HasSynthesisTailBound f K →
      ‖finiteSynthesis f (fun _ => 1)‖ ^ 2 ≤
        C * K ^ 2 * (n : ℝ) ^ growthExponent K * ∑ j, ‖f j‖ ^ 2

end ProofProject
