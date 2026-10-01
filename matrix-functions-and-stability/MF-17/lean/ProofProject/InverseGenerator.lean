import ProofProject.LaplaceGenerator
import ProofProject.GeneratorOrbit

/-! Existence and uniqueness of the bounded inverse for the full generator. -/

noncomputable section

namespace ProofProject

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H]

/-- Both inverse identities follow from strong integration and right derivatives. -/
theorem StableSemigroup.isGeneratorInverse_laplaceInverse (T : StableSemigroup M H) :
    IsGeneratorInverse T T.laplaceInverse := by
  intro x y
  constructor
  · exact GeneratorGraph.laplaceInverse_eq
  · intro h
    simpa only [h] using T.laplaceInverse_graph y

/-- Every bounded inverse agrees with the strong Laplace integral. -/
theorem IsGeneratorInverse.eq_laplaceInverse {T : StableSemigroup M H} {B : H →L[ℂ] H}
    (hB : IsGeneratorInverse T B) : B = T.laplaceInverse :=
  hB.unique T.isGeneratorInverse_laplaceInverse

/-- The normalization of the decay rate gives the uniform inverse bound M. -/
theorem IsGeneratorInverse.norm_le {T : StableSemigroup M H} {B : H →L[ℂ] H}
    (hB : IsGeneratorInverse T B) (hM : 0 ≤ M) : ‖B‖ ≤ M := by
  rw [hB.eq_laplaceInverse]
  exact T.norm_laplaceInverse_le hM

end ProofProject
