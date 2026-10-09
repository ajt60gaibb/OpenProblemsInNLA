import ProofProject.Definitions

/-! Basic facts about the full generator graph and its bounded inverse. -/

noncomputable section

namespace ProofProject

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]

namespace GeneratorGraph

 theorem unique {T : StableSemigroup M H} {x y z : H}
    (hy : GeneratorGraph T x y) (hz : GeneratorGraph T x z) : y = z := by
  exact (hy.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (hz.derivWithin (uniqueDiffWithinAt_Ici 0))

 theorem zero (T : StableSemigroup M H) : GeneratorGraph T 0 0 := by
  simpa [GeneratorGraph] using
    (hasDerivWithinAt_const (0 : ℝ) (Set.Ici 0) (0 : H))

 theorem add {T : StableSemigroup M H} {x y x' y' : H}
    (h : GeneratorGraph T x y) (h' : GeneratorGraph T x' y') :
    GeneratorGraph T (x + x') (y + y') := by
  simpa only [GeneratorGraph, map_add, Pi.add_def] using HasDerivWithinAt.add h h'

 theorem smul {T : StableSemigroup M H} {x y : H}
    (h : GeneratorGraph T x y) (c : ℂ) : GeneratorGraph T (c • x) (c • y) := by
  simpa only [GeneratorGraph, map_smul, Pi.smul_def] using HasDerivWithinAt.const_smul c h

end GeneratorGraph

namespace IsGeneratorInverse

 theorem graph {T : StableSemigroup M H} {B : H →L[ℂ] H}
    (hB : IsGeneratorInverse T B) (y : H) : GeneratorGraph T (B y) y :=
  (hB (B y) y).mpr rfl

 theorem unique {T : StableSemigroup M H} {B C : H →L[ℂ] H}
    (hB : IsGeneratorInverse T B) (hC : IsGeneratorInverse T C) : B = C := by
  ext y
  exact (hB (C y) y).mp (hC.graph y)

 theorem injective {T : StableSemigroup M H} {B : H →L[ℂ] H}
    (hB : IsGeneratorInverse T B) : Function.Injective B := by
  intro y z hyz
  exact (hB.graph y).unique (hyz.symm ▸ hB.graph z)

 theorem range_eq_domain {T : StableSemigroup M H} {B : H →L[ℂ] H}
    (hB : IsGeneratorInverse T B) :
    Set.range B = {x : H | ∃ y : H, GeneratorGraph T x y} := by
  ext x
  exact exists_congr fun y => (hB x y).symm

end IsGeneratorInverse

@[simp] theorem inverseEvolution_zero (B : H →L[ℂ] H) :
    inverseEvolution B 0 = ContinuousLinearMap.id ℂ H := by
  simp only [inverseEvolution, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
  rfl

end ProofProject
