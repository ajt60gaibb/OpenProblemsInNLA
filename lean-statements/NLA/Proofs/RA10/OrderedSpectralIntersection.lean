import NLA.Proofs.RA10.OrderedSpectralRayleigh
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! RA-10 finite-dimensional geometric gate: one nonzero vector lies in the
supplied C-basis prefix and supplied A-basis suffix coordinate cuts. The
compression eigenvalue comparison and full target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

theorem orderedSpectral_prefix_suffix_nonzero_intersection {n : ℕ}
    (QC QA : Matrix (Fin n) (Fin n) ℝ) (a : Fin n) :
    ∃ x : Fin n → ℝ,
      x ≠ 0 ∧
        (∀ b : Fin n, a.val < b.val →
          (∑ i : Fin n, x i * QC i b) = 0) ∧
        (∀ b : Fin n, b.val < a.val →
          (∑ i : Fin n, x i * QA i b) = 0) := by
  classical
  let T : (Fin n → ℝ) →ₗ[ℝ] ({b : Fin n // b ≠ a} → ℝ) :=
    LinearMap.pi fun b =>
      if b.val.val < a.val then
        ((LinearMap.proj (R := ℝ) b.val : (Fin n → ℝ) →ₗ[ℝ] ℝ).comp
          QA.transpose.mulVecLin)
      else
        ((LinearMap.proj (R := ℝ) b.val : (Fin n → ℝ) →ₗ[ℝ] ℝ).comp
          QC.transpose.mulVecLin)
  have hcard : Fintype.card {b : Fin n // b ≠ a} < Fintype.card (Fin n) :=
    Fintype.card_subtype_lt (p := fun b : Fin n => b ≠ a) (x := a) (by simp)
  have hdim : Module.finrank ℝ ({b : Fin n // b ≠ a} → ℝ) <
      Module.finrank ℝ (Fin n → ℝ) := by
    simpa only [Module.finrank_fintype_fun_eq_card] using hcard
  have hker : LinearMap.ker T ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨x, hxker, hxne⟩ := (LinearMap.ker T).ne_bot_iff.mp hker
  have hTx : T x = 0 := LinearMap.mem_ker.mp hxker
  refine ⟨x, hxne, ?_, ?_⟩
  · intro b hb
    have hba : b ≠ a := Fin.ne_of_gt (Fin.lt_def.mpr hb)
    have hbT := congrFun hTx ⟨b, hba⟩
    have hnot : ¬ b.val < a.val := Nat.not_lt.mpr (Nat.le_of_lt hb)
    simp only [T, LinearMap.pi_apply, hnot, ite_false,
      LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply,
      Pi.zero_apply] at hbT
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using hbT
  · intro b hb
    have hba : b ≠ a := Fin.ne_of_lt (Fin.lt_def.mpr hb)
    have hbT := congrFun hTx ⟨b, hba⟩
    simp only [T, LinearMap.pi_apply, hb, ite_true,
      LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply,
      Pi.zero_apply] at hbT
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using hbT

#assert_trust kernel orderedSpectral_prefix_suffix_nonzero_intersection
#print axioms orderedSpectral_prefix_suffix_nonzero_intersection

end NLA.Proofs.RA10
