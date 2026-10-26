import NLA.Proofs.TR04.SVDTieFull

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped InnerProductSpace BigOperators Matrix
namespace NLA.Proofs.TR04.SVD

theorem starProjection_span_orthonormal {ι : Type*} [Fintype ι] {m : ℕ}
    {v : ι → Space m} (hv : Orthonormal ℝ v) (x : Space m) :
    (Submodule.span ℝ (Set.range v)).starProjection x = ∑ i, ⟪v i, x⟫_ℝ • v i := by
  classical
  let S := Submodule.span ℝ (↑(Finset.univ.image v) : Set (Space m))
  let b := OrthonormalBasis.span hv Finset.univ
  have h := congrArg (fun y : S => (y : Space m))
    (b.orthogonalProjectionOnto_apply_eq_sum x)
  have hb (i : (Finset.univ : Finset ι)) : (b i : Space m) = v i.val :=
    OrthonormalBasis.span_apply hv Finset.univ i
  simp only [Submodule.coe_sum, Submodule.coe_smul, hb] at h
  simpa [S] using h

def frameSpace {m : ℕ} {ι : Type*} (Q : Matrix (Fin m) ι ℝ) : Submodule ℝ (Space m) :=
  Submodule.span ℝ (Set.range (fun j => WithLp.toLp 2 (fun i => Q i j)))

theorem orthonormal_frameColumns {m : ℕ} {ι : Type*} [DecidableEq ι]
    {Q : Matrix (Fin m) ι ℝ} (hQ : OrthonormalColumns Q) :
    Orthonormal ℝ (fun j => (WithLp.toLp 2 (fun i => Q i j) : Space m)) := by
  rw [orthonormal_iff_ite]
  intro i j
  simpa [PiLp.inner_apply, mul_comm] using hQ i j

/-- The actual span projector of any orthonormal frame is its actual matrix
product QQᵀ. This identifies the tensor contraction/lift operation exactly. -/
theorem frame_projectMatrix {m l : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Matrix (Fin m) ι ℝ} (hQ : OrthonormalColumns Q)
    (B : Matrix (Fin m) (Fin l) ℝ) :
    projectMatrix (frameSpace Q) B = Q * (Q.transpose * B) := by
  ext i j
  change (Submodule.span ℝ (Set.range
    (fun k => (WithLp.toLp 2 (fun a => Q a k) : Space m)))).starProjection
      (matrixColumn B j) i = _
  rw [starProjection_span_orthonormal (orthonormal_frameColumns hQ)]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, PiLp.inner_apply,
    matrixColumn]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem selectedFrame_projectMatrix {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (P : Fin (min m l) → Prop) [DecidablePred P]
    (B : Matrix (Fin m) (Fin l) ℝ) :
    selectedFrame U P * ((selectedFrame U P).transpose * B) =
      projectMatrix (singularSubspace U P) B := by
  have h := frame_projectMatrix (orthonormalColumns_selectedFrame hU P) B
  exact h.symm

theorem exists_directionFrame {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (S : Finset (Fin (min m l))) :
    ∃ Q : Matrix (Fin m) (Fin S.card) ℝ, OrthonormalColumns Q ∧
      ∀ B : Matrix (Fin m) (Fin l) ℝ,
        Q * (Q.transpose * B) = projectMatrix (directionSubspace U S) B := by
  classical
  let e : {k // k ∈ S} ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe S)
  let Q := (selectedFrame U (fun k => k ∈ S)).submatrix id e.symm
  have hQ : OrthonormalColumns Q := orthonormalColumns_submatrix
    (orthonormalColumns_selectedFrame hU _) e.symm e.symm.injective
  have hspace : frameSpace Q = directionSubspace U S := by
    unfold frameSpace directionSubspace singularSubspace
    congr 1
    exact e.symm.surjective.range_comp (fun k : {k // k ∈ S} =>
      matrixColumn U (Fin.castLE (Nat.min_le_left m l) k.val))
  refine ⟨Q, hQ, fun B => ?_⟩
  rw [← frame_projectMatrix hQ B, hspace]

theorem TieStructure.exists_frame {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)} (T : TieStructure sigma a)
    (j : Fin T.tied) :
    ∃ Q : Matrix (Fin m) (Fin (a.val + 1)) ℝ, OrthonormalColumns Q ∧
      ∀ B : Matrix (Fin m) (Fin l) ℝ,
        Q * (Q.transpose * B) = projectMatrix
          (directionSubspace U (tieSelection T.above T.tied T.fits T.take j)) B := by
  have hc : (tieSelection T.above T.tied T.fits T.take j).card = a.val + 1 := by
    rw [card_tieSelection T.fits T.take T.take_le j, T.rank_eq]
  have hx := exists_directionFrame (l := l) hU
    (tieSelection T.above T.tied T.fits T.take j)
  rw [hc] at hx
  exact hx

#assert_trust kernel frame_projectMatrix
#assert_trust kernel selectedFrame_projectMatrix
#assert_trust kernel TieStructure.exists_frame
#print axioms TieStructure.exists_frame
end NLA.Proofs.TR04.SVD
