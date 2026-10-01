import ProofProject.EndpointDeficit

/-!
# Hilbert families in a larger universe

The usual `ULift` norm is retained. The inner product is pulled back along
`ULift.down`, and the resulting linear isometry preserves the boundary
estimate and every finite synthesis norm.
-/

noncomputable section

namespace ProofProject

universe u v w

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The existing lifted norm comes from the original inner product. -/
instance uliftInnerProductSpace : InnerProductSpace ℂ (ULift.{v} H) where
  toNormedSpace := ULift.normedSpace
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := InnerProductSpace.norm_sq_eq_re_inner x.down
  conj_inner_symm x y := InnerProductSpace.conj_inner_symm x.down y.down
  add_left x y z := InnerProductSpace.add_left x.down y.down z.down
  smul_left x y r := InnerProductSpace.smul_left x.down y.down r

@[simp] theorem inner_ulift (x y : ULift.{v} H) :
    inner ℂ x y = inner ℂ x.down y.down := rfl

/-- The canonical complex-linear isometry into a higher universe. -/
def uliftHilbert (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    H ≃ₗᵢ[ℂ] ULift.{v} H :=
  (LinearIsometryEquiv.ulift ℂ H).symm

@[simp] theorem uliftHilbert_apply (x : H) :
    uliftHilbert.{u, v} H x = ULift.up x := rfl

@[simp] theorem uliftHilbert_inner (x y : H) :
    inner ℂ (uliftHilbert.{u, v} H x) (uliftHilbert.{u, v} H y) =
      inner ℂ x y := rfl

variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {n : ℕ}

lemma finiteSynthesis_map_isometry (e : H →ₗᵢ[ℂ] K)
    (f : Fin n → H) (a : Fin n → ℂ) :
    finiteSynthesis (fun i => e (f i)) a = e (finiteSynthesis f a) := by
  simp only [finiteSynthesis, map_sum, map_smul]

lemma replicationBase_map_isometry (e : H →ₗᵢ[ℂ] K)
    (f : Fin n → H) (a : Fin n → ℂ) (i : Fin n) :
    replicationBase (fun j => e (f j)) a i = e (replicationBase f a i) := by
  simp only [replicationBase, map_sum, apply_ite, map_zero, map_smul]

lemma replicationTail_map_isometry (e : H →ₗᵢ[ℂ] K)
    (f : Fin n → H) (a : Fin n → ℂ) (i : Fin n) :
    replicationTail (fun j => e (f j)) a i = e (replicationTail f a i) := by
  simp only [replicationTail, map_sum, apply_ite, map_zero, map_smul]

lemma coefficientDeficit_map_isometry (e : H →ₗᵢ[ℂ] K)
    (M : ℝ) (x y z : H) (t s : ℂ) :
    coefficientDeficit M (e x) (e y) (e z) t s = coefficientDeficit M x y z t s := by
  simp only [coefficientDeficit, ← map_smul, ← map_add, e.norm_map]

/-- No surjectivity is needed to preserve either endpoint boundary estimate. -/
theorem HasBoundaryEstimate.linearIsometry (e : H →ₗᵢ[ℂ] K)
    {f : Fin n → H} {M B : ℝ} (hf : HasBoundaryEstimate f M B) :
    HasBoundaryEstimate (fun i => e (f i)) M B := by
  intro a i t
  simpa only [replicationBase_map_isometry, replicationTail_map_isometry,
    coefficientDeficit_map_isometry, ← map_smul, ← map_add,
    e.inner_map_map] using hf a i t

@[simp] theorem finiteSynthesis_ulift_norm (f : Fin n → H) (a : Fin n → ℂ) :
    ‖finiteSynthesis (fun i => (ULift.up (f i) : ULift.{v} H)) a‖ =
      ‖finiteSynthesis f a‖ := by
  change ‖finiteSynthesis (fun i => (uliftHilbert.{u, v} H).toLinearIsometry (f i)) a‖ = _
  rw [finiteSynthesis_map_isometry, LinearIsometry.norm_map]

/-- The source boundary constant is unchanged when its family is lifted. -/
theorem HasBoundaryEstimate.ulift {f : Fin n → H} {M B : ℝ}
    (hf : HasBoundaryEstimate f M B) :
    HasBoundaryEstimate (fun i => (ULift.up (f i) : ULift.{v} H)) M B :=
  hf.linearIsometry (uliftHilbert.{u, v} H).toLinearIsometry

end ProofProject
