import NLA.Proofs.TR04.SVDCore

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped InnerProductSpace BigOperators

namespace NLA.Proofs.TR04.SVD

theorem image_rightBasis_eq_smul {m l : ℕ} (T : Space l →ₗ[ℝ] Space m)
    (u : OrthonormalBasis (Fin m) ℝ (Space m))
    (hu : ∀ i, i.val < Module.finrank ℝ T.range → u i = leftVector T i)
    (i : Fin l) (j : Fin m) (hij : i.val = j.val) :
    T (rightBasis T i) = T.singularValues i.val • u j := by
  by_cases hi : i.val < Module.finrank ℝ T.range
  · have hj : j.val < Module.finrank ℝ T.range := hij ▸ hi
    have hjl : j.val < l := hij ▸ i.isLt
    have hp : 0 < T.singularValues i.val :=
      T.singularValues_pos_iff_lt_finrank_range.mpr hi
    have hjv : (⟨j.val, hjl⟩ : Fin l) = i := Fin.ext hij.symm
    rw [hu j hj, leftVector, dif_pos hjl, hjv, ← hij, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hp), one_smul]
  · have hz := T.singularValues_eq_zero_iff_le_finrank_range.mpr (Nat.le_of_not_gt hi)
    rw [image_rightBasis_eq_zero T i (Nat.le_of_not_gt hi), hz, zero_smul]

/-- Discard a terminal interval whose entries vanish, including either empty interval. -/
theorem sum_fin_truncate {a b : ℕ} (hab : a ≤ b) (f : Fin b → ℝ)
    (hz : ∀ i, a ≤ i.val → f i = 0) :
    ∑ i : Fin b, f i = ∑ i : Fin a, f (Fin.castLE hab i) := by
  classical
  let e : Fin a → Fin b := Fin.castLE hab
  have he : Function.Injective e := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin b => k.val) h)
  have hs : ∑ i ∈ Finset.univ.image e, f i = ∑ i : Fin a, f (e i) := by
    rw [Finset.sum_image]
    exact fun i _ j _ h => he h
  rw [← hs]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply hz
  by_contra hn
  have hia : i.val < a := Nat.lt_of_not_ge hn
  apply hi
  exact Finset.mem_image.mpr ⟨⟨i.val, hia⟩, Finset.mem_univ _, Fin.ext rfl⟩

/-- Every finite real rectangular matrix has a full SVD in the machine's exact
model. No dimension, rank, or basis selection hypothesis is imposed. -/
theorem exists_validSVD {m l : ℕ} (B : Matrix (Fin m) (Fin l) ℝ) :
    ∃ U sigma V, NLA.Computation.SVDMachine.ValidSVD B U sigma V := by
  classical
  let T : Space l →ₗ[ℝ] Space m := Matrix.toEuclideanLin B
  let v := rightBasis T
  obtain ⟨u, hu⟩ := exists_leftBasis T
  let U : Matrix (Fin m) (Fin m) ℝ := fun i j => u j i
  let V : Matrix (Fin l) (Fin l) ℝ := fun i j => v j i
  let sigma : Fin (min m l) → ℝ := fun k => T.singularValues k.val
  refine ⟨U, sigma, V, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa [U, PiLp.inner_apply, real_inner_comm, mul_comm] using u.inner_eq_ite i j
  · intro i j
    simpa [V, PiLp.inner_apply, real_inner_comm, mul_comm] using v.inner_eq_ite i j
  · intro k
    exact T.singularValues_nonneg k.val
  · intro i j hij
    exact T.singularValues_antitone hij
  · intro i j
    have hsum := congrArg (fun x : Space l => (T x) i)
      (v.sum_repr' (EuclideanSpace.single j (1 : ℝ)))
    have hcol : T (EuclideanSpace.single j (1 : ℝ)) i = B i j := by
      simp [T, Matrix.toLpLin_apply]
    have hcoords : B i j = ∑ k : Fin l, v k j * T (v k) i := by
      rw [← hcol]
      symm
      simpa only [map_sum, map_smul, EuclideanSpace.inner_single_right,
        RCLike.conj_to_real, one_mul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
        smul_eq_mul] using hsum
    rw [hcoords]
    have hz : ∀ k : Fin l, min m l ≤ k.val → v k j * T (v k) i = 0 := by
      intro k hk
      have hq : Module.finrank ℝ T.range ≤ min m l :=
        le_min (range_finrank_le_codomain T) (range_finrank_le_domain T)
      rw [show T (v k) = 0 from image_rightBasis_eq_zero T k (hq.trans hk)]
      simp
    rw [sum_fin_truncate (Nat.min_le_right m l) _ hz]
    apply Finset.sum_congr rfl
    intro k _
    let kl : Fin l := Fin.castLE (Nat.min_le_right m l) k
    let km : Fin m := Fin.castLE (Nat.min_le_left m l) k
    have himg := image_rightBasis_eq_smul T u hu kl km rfl
    change v kl j * T (v kl) i = U i km * sigma k * V j kl
    rw [show T (v kl) = T.singularValues kl.val • u km from himg]
    simp only [PiLp.smul_apply, smul_eq_mul, U, V, sigma]
    change v kl j * (T.singularValues k.val * u km i) =
      u km i * T.singularValues k.val * v kl j
    ring

#assert_trust kernel exists_validSVD
#print axioms exists_validSVD

end NLA.Proofs.TR04.SVD
