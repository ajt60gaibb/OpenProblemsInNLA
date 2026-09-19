import NLA.PF03.TriangleCertificate
import NLA.PF03.QuadraticGeneratorCertificate
import NLA.PF03.CrossConeSigns0
import NLA.PF03.CrossConeSigns1
import NLA.PF03.CrossConeSigns2
import NLA.PF03.CrossConeSigns3
import NLA.PF03.CrossConeSigns4
import NLA.PF03.CrossConeSigns5

/-!
C10: every ordered cross-cone pairing is strictly positive for the actual
defined generator columns and quadraticSeed. The rational cache is linked by
all 147 cubic identities and the C09 generator identity; every sign consumes
the checked alpha enclosure through cubicLower.
Original mathematics and seed: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

theorem generator_entry_cache (i : Fin 7) (a : Fin 3) (r : Fin 7) :
    generator i a r = RawData.generators r (generatorIndex i a) := by
  have h := congrArg (fun M : QMat 7 21 => M r (generatorIndex i a))
    triangle_certificate.2.2.2.2.2
  simpa only [generatorMatrix, generatorIndex, Equiv.symm_apply_apply] using h

theorem crossCubic_eval (i j : Fin 7) (a b : Fin 3) :
    cubicEval (crossCubic i j a b) =
      bilinear quadraticSeed (castVector (generator i a)) (castVector (generator j b)) := by
  change cubicEval (crossCubic i j a b) =
    ∑ r : Fin 7, ∑ s : Fin 7, (generator i a r : ℝ) *
      cubicEval (RawData.quadraticMatrix r s) * (generator j b s : ℝ)
  simp only [crossCubic, cubicEval_finset_sum, cubicEval_cubicScale,
    generator_entry_cache]
  apply Finset.sum_congr rfl
  intro r _
  rw [← quadraticGeneratorCubic_cache r (generatorIndex j b),
    quadraticGeneratorCubic_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem cross_cone_lower (i j : Fin 7) (hij : i < j) (a b : Fin 3) :
    0 < cubicLower (crossCubic i j a b) := by
  fin_cases i
  · exact cross_cone_lower0 j hij a b
  · exact cross_cone_lower1 j hij a b
  · exact cross_cone_lower2 j hij a b
  · exact cross_cone_lower3 j hij a b
  · exact cross_cone_lower4 j hij a b
  · exact cross_cone_lower5 j hij a b
  · change 6 < j.val at hij
    have hj : j.val < 7 := j.isLt
    omega

/-- C10: exact unchanged frozen real bilinear statement. -/
theorem cross_cone_certificate (i j : Fin 7) (hij : i < j) (a b : Fin 3) :
    0 < bilinear quadraticSeed (castVector (generator i a)) (castVector (generator j b)) := by
  have h := cubicEval_pos_of_lower (crossCubic i j a b) (cross_cone_lower i j hij a b)
  rwa [crossCubic_eval] at h

#print axioms cross_cone_certificate
#assert_trust kernel cross_cone_certificate

end NLA.PF03
