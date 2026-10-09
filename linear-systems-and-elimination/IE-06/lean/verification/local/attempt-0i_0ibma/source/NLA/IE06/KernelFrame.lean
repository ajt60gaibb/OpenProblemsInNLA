/- Fixed Euclidean nullspace frames; no measurable-choice assertion.
The exact contract is part of the independently approved B4 specification. -/
import NLA.IE06.Spectral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open Matrix Module WithLp
open scoped BigOperators
namespace NLA.IE06.KernelFrame
open Spectral

theorem exists_kernel_frame {m s : ℕ} (M : Matrix (Fin m) (Fin (m+s)) ℝ)
    (hM : Function.Surjective (euclideanMap M)) :
    ∃ Q : Matrix (Fin (m+s)) (Fin s) ℝ,
      Qᴴ * Q = 1 ∧ (euclideanMap Q).range = (euclideanMap M).ker := by
  let K := (euclideanMap M).ker
  have hr : finrank ℝ (euclideanMap M).range = m := by
    rw [LinearMap.range_eq_top.mpr hM]
    simp
  have hk : finrank ℝ K = s := by
    have h := LinearMap.finrank_range_add_finrank_ker (euclideanMap M)
    rw [hr] at h
    simp only [finrank_euclideanSpace, Fintype.card_fin] at h
    dsimp [K]
    omega
  let b : OrthonormalBasis (Fin s) ℝ K := (stdOrthonormalBasis ℝ K).reindex (finCongr hk)
  let Q : Matrix (Fin (m+s)) (Fin s) ℝ := fun i j => (b j).val i
  have happ (x : EuclideanSpace ℝ (Fin s)) :
      euclideanMap Q x = (b.repr.symm x).val := by
    have he := congrArg (fun z : K => z.val) (b.sum_repr_symm x)
    rw [← he]
    ext i
    change (∑ j, Q i j * x j) = _
    simp [Q,mul_comm]
  refine ⟨Q,?_,?_⟩
  · ext i j
    have he : (Qᴴ * Q) i j = inner ℝ (b i) (b j) := by
      change (Qᴴ * Q) i j = inner ℝ (b i).val (b j).val
      change (∑ k, Q k i * Q k j) = _
      simp only [Q,PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    rw [he,b.inner_eq_ite]
    simp only [Matrix.one_apply]
  · ext x
    constructor
    · rintro ⟨y,rfl⟩
      rw [happ]
      exact (b.repr.symm y).property
    · intro hx
      refine ⟨b.repr ⟨x,hx⟩,?_⟩
      rw [happ]
      simp

#assert_trust kernel exists_kernel_frame
#print axioms exists_kernel_frame
end NLA.IE06.KernelFrame
