import NLA.PF03.Definitions
import LeanCert.Tactic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
C18 from the independently approved PF-03 statement packet. Literal absence
of lines forces a zero real kernel and then a zero rational kernel. A rational
linear left inverse exists in all dimensions, including dimension zero.

Original mathematics and seed: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, with Codex assistance. Proof author: /root; final independent
proof reviewers must be nonauthors.
-/

set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

theorem pointed_halfspaces_injective {N d : ℕ} (R : QMat N d)
    (hR : NoLine (HSet R)) :
    (∀ x : Fin d → ℝ, (castMatrix R).mulVec x = 0 → x = 0) ∧
      (∀ x : Fin d → ℚ, R.mulVec x = 0 → x = 0) ∧
      ∃ L : QMat d N, L * R = 1 := by
  have hreal : ∀ x : Fin d → ℝ, (castMatrix R).mulVec x = 0 → x = 0 := by
    intro x hx
    apply hR x
    · intro i
      simp only [hx, Pi.zero_apply, le_refl]
    · intro i
      simp only [Matrix.mulVec_neg, hx, neg_zero, Pi.zero_apply, le_refl]
  have hrat : ∀ x : Fin d → ℚ, R.mulVec x = 0 → x = 0 := by
    intro x hx
    have hc : (castMatrix R).mulVec (fun j => (x j : ℝ)) = 0 := by
      ext i
      have hi := congrArg (fun q : ℚ => (q : ℝ)) (congrFun hx i)
      simpa [castMatrix, Matrix.map, Matrix.mulVec, dotProduct] using hi
    have hz := hreal _ hc
    ext j
    have hj : (x j : ℝ) = 0 := congrFun hz j
    exact_mod_cast hj
  refine ⟨hreal, hrat, ?_⟩
  have hk : LinearMap.ker R.mulVecLin = ⊥ :=
    Matrix.ker_mulVecLin_eq_bot_iff.mpr hrat
  obtain ⟨g, hg⟩ := R.mulVecLin.exists_leftInverse_of_injective hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have hg' : g.comp (Matrix.toLin' R) = LinearMap.id := hg
  have hm := congrArg (fun f : (Fin d → ℚ) →ₗ[ℚ] (Fin d → ℚ) =>
    LinearMap.toMatrix' f) hg'
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_id] using hm

#print axioms pointed_halfspaces_injective
#assert_trust kernel pointed_halfspaces_injective

end NLA.PF03
