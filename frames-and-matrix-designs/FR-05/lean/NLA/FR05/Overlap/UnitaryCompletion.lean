import NLA.FR05.Overlap.HaarCorner
import NLA.FR05.Gaussian.GaussianGram

set_option autoImplicit false
noncomputable section
open Matrix WithLp
open scoped BigOperators

namespace NLA.FR05

theorem exists_sourceUnitary_extension {n k : ℕ} (hk : k ≤ n)
    (B : Matrix (Fin n) (Fin k) ℂ) (hB : Bᴴ * B = 1) :
    ∃ U : SourceUnitary n, ∀ i j, U.val i (Fin.castLE hk j) = B i j := by
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun j ↦
    if h : j.val < k then toLp 2 (fun i ↦ B i ⟨j.val, h⟩) else 0
  let s : Set (Fin n) := {j | j.val < k}
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i.val.val < k := i.property
    have hj : j.val.val < k := j.property
    have hij : (⟨i.val.val, hi⟩ : Fin k) = ⟨j.val.val, hj⟩ ↔ i = j := by
      simp only [Subtype.ext_iff, Fin.ext_iff]
    have h := congrFun (congrFun hB ⟨i.val.val, hi⟩) ⟨j.val.val, hj⟩
    simpa [v, Set.domRestrict, hi, hj, PiLp.inner_apply, RCLike.inner_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hij, mul_comm]
      using h
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n))
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  refine ⟨⟨e.toBasis.toMatrix b, e.toMatrix_orthonormalBasis_mem_unitary b⟩, ?_⟩
  intro i j
  have hj : Fin.castLE hk j ∈ s := j.isLt
  have hbj := hb (Fin.castLE hk j) hj
  simp only [v] at hbj
  change e.toBasis.repr (b (Fin.castLE hk j)) i = B i j
  rw [hbj]
  simp [e]

theorem exists_sourceUnitary_firstColumn {n : ℕ} (hn : 0 < n) (v : Signal n)
    (hv : signalEnergy v = 1) :
    ∃ U : SourceUnitary n, ∀ i, U.val i ⟨0, hn⟩ = v i := by
  let B : Matrix (Fin n) (Fin 1) ℂ := fun i _ ↦ v i
  have hB : Bᴴ * B = 1 := by
    ext i j
    have h : (∑ l, star (v l) * v l) = (1 : ℂ) := by
      rw [show (∑ l, star (v l) * v l) = (signalEnergy v : ℂ) by
        simp [signalEnergy, squaredEuclideanNorm, Complex.normSq_eq_conj_mul_self]]
      exact_mod_cast hv
    change (∑ l, star (v l) * v l) = if i = j then 1 else 0
    rw [if_pos (Subsingleton.elim i j)]
    exact h
  obtain ⟨U, hU⟩ := exists_sourceUnitary_extension (by lia : 1 ≤ n) B hB
  exact ⟨U, fun i ↦ hU i 0⟩

end NLA.FR05
