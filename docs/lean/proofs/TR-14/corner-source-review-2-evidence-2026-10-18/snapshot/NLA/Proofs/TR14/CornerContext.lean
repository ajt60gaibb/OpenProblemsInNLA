import NLA.Proofs.TR14.CornerProduct
import NLA.Proofs.TR14.ContextualIteration

/-! Actual restriction of contextual graph data to an idempotent block.
All spaces are actual images under quotient algebra maps and the functional
is the original functional composed with the ambient block inclusion. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

noncomputable section
variable {K A C : Type*} [Field K] [CommRing A] [CommRing C]
  [Algebra K A] [Algebra K C]

/-- The idempotent has value one in its own genuine quotient algebra. -/
@[simp] theorem cornerProjection_self (e : A) :
    cornerProjection (K := K) e e = 1 := by
  have h : cornerProjection (K := K) e (1 - e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

/-- Quotient projection is a left inverse to the actual ambient inclusion. -/
@[simp] theorem cornerProjection_inclusion (e : A) (he : e * e = e)
    (x : IdempotentCorner e) :
    cornerProjection (K := K) e (cornerInclusion (K := K) e he x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (Ideal.span ({1 - e} : Set A)) x
  change cornerProjection (K := K) e
    (cornerInclusion (K := K) e he (cornerProjection (K := K) e a)) = cornerProjection (K := K) e a
  rw [cornerInclusion_projection, map_mul, cornerProjection_self, one_mul]

/-- The actual inclusion lies in the ambient idempotent multiplication block. -/
@[simp] theorem cornerInclusion_idempotent_mul (e : A) (he : e * e = e)
    (x : IdempotentCorner e) : e * cornerInclusion (K := K) e he x =
      cornerInclusion (K := K) e he x := by
  calc
    e * cornerInclusion (K := K) e he x =
        cornerInclusion (K := K) e he 1 * cornerInclusion (K := K) e he x :=
      congrArg (fun z : A => z * cornerInclusion (K := K) e he x)
        (cornerInclusion_one (K := K) e he).symm
    _ = cornerInclusion (K := K) e he (1 * x) := (cornerInclusion_mul e he 1 x).symm
    _ = cornerInclusion (K := K) e he x := by rw [one_mul]

/-- Genuine block quotient map to the first and scalar component corners. -/
def cornerBlockProjection (e : A × C) :
    (A × C) →ₐ[K] (IdempotentCorner e.1 × IdempotentCorner e.2) :=
  (cornerProjection (K := K) e.1).prodMap (cornerProjection (K := K) e.2)

/-- Genuine ambient inclusion of that product corner. -/
def cornerBlockInclusion (e : A × C) (he : e * e = e) :
    (IdempotentCorner e.1 × IdempotentCorner e.2) →ₗ[K] (A × C) :=
  (cornerInclusion (K := K) e.1 (congrArg Prod.fst he)).prodMap
    (cornerInclusion (K := K) e.2 (congrArg Prod.snd he))

@[simp] theorem cornerBlockInclusion_projection (e : A × C) (he : e * e = e) (x : A × C) :
    cornerBlockInclusion (K := K) e he (cornerBlockProjection (K := K) e x) = e * x := rfl

@[simp] theorem cornerBlockInclusion_one (e : A × C) (he : e * e = e) :
    cornerBlockInclusion (K := K) e he 1 = e := by
  apply Prod.ext <;> simp [cornerBlockInclusion]

theorem cornerBlockInclusion_mul (e : A × C) (he : e * e = e)
    (x y : IdempotentCorner e.1 × IdempotentCorner e.2) :
    cornerBlockInclusion (K := K) e he (x * y) =
      cornerBlockInclusion (K := K) e he x * cornerBlockInclusion (K := K) e he y := by
  apply Prod.ext <;> simp only [cornerBlockInclusion, LinearMap.prodMap_apply,
    Prod.fst_mul, Prod.snd_mul, cornerInclusion_mul]

theorem cornerBlockInclusion_injective (e : A × C) (he : e * e = e) :
    Function.Injective (cornerBlockInclusion (K := K) e he) := by
  intro x y hxy
  apply Prod.ext
  · exact cornerInclusion_injective (K := K) e.1 (congrArg Prod.fst he) (congrArg Prod.fst hxy)
  · exact cornerInclusion_injective (K := K) e.2 (congrArg Prod.snd he) (congrArg Prod.snd hxy)

/-- Projection and ambient inclusion are exact inverses on the intrinsic block. -/
@[simp] theorem cornerBlockProjection_inclusion (e : A × C) (he : e * e = e)
    (x : IdempotentCorner e.1 × IdempotentCorner e.2) :
    cornerBlockProjection (K := K) e (cornerBlockInclusion (K := K) e he x) = x := by
  change (cornerProjection (K := K) e.1
      (cornerInclusion (K := K) e.1 (congrArg Prod.fst he) x.1),
    cornerProjection (K := K) e.2
      (cornerInclusion (K := K) e.2 (congrArg Prod.snd he) x.2)) = x
  apply Prod.ext <;> simp only [cornerProjection_inclusion]

/-- Actual image mode or product space in the intrinsic product corner. -/
def cornerBlockSpace (e : A × C) (U : Submodule K (A × C)) :
    Submodule K (IdempotentCorner e.1 × IdempotentCorner e.2) :=
  U.map (cornerBlockProjection (K := K) e).toLinearMap

/-- The intrinsic functional evaluates the actual ambient block component. -/
def cornerBlockFunctional (e : A × C) (he : e * e = e) (Λ : (A × C) →ₗ[K] K) :
    (IdempotentCorner e.1 × IdempotentCorner e.2) →ₗ[K] K :=
  Λ.comp (cornerBlockInclusion (K := K) e he)

@[simp] theorem cornerBlockFunctional_projection (e : A × C) (he : e * e = e)
    (Λ : (A × C) →ₗ[K] K) (x : A × C) :
    cornerBlockFunctional (K := K) e he Λ (cornerBlockProjection (K := K) e x) =
      Λ (e * x) := rfl

/-- The ambient image is exactly the actual idempotent-multiplied subspace. -/
theorem cornerBlockSpace_inclusion (e : A × C) (he : e * e = e)
    (U : Submodule K (A × C)) :
    (cornerBlockSpace (K := K) e U).map (cornerBlockInclusion (K := K) e he) =
      U.map (LinearMap.mulLeft K e) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨cornerBlockProjection (K := K) e z, ⟨z, hz, rfl⟩, rfl⟩

/-- One-containing modes map to modes containing the actual block identity. -/
theorem one_mem_cornerBlockSpace (e : A × C) (U : Submodule K (A × C))
    (hU : (1 : A × C) ∈ U) :
    (1 : IdempotentCorner e.1 × IdempotentCorner e.2) ∈ cornerBlockSpace (K := K) e U :=
  ⟨1, hU, (cornerBlockProjection (K := K) e).map_one⟩

/-- Algebra images commute with finite list products of actual subspaces. -/
theorem submodule_map_list_prod {B D : Type*} [CommRing B] [CommRing D]
    [Algebra K B] [Algebra K D] (f : B →ₐ[K] D) (L : List (Submodule K B)) :
    (L.map (fun U => U.map f.toLinearMap)).prod = L.prod.map f.toLinearMap := by
  induction L with
  | nil => exact (Submodule.map_one f).symm
  | cons U L ih =>
      simp only [List.map_cons, List.prod_cons, ih, Submodule.map_mul]

/-- Whole products in the block are the actual image of the whole product. -/
theorem cornerBlockSpace_list_prod (e : A × C) (L : List (Submodule K (A × C))) :
    (L.map (cornerBlockSpace (K := K) e)).prod = cornerBlockSpace (K := K) e L.prod :=
  submodule_map_list_prod (cornerBlockProjection (K := K) e) L

/-- A stabilizing idempotent and the original annihilation imply actual
annihilation of its intrinsic block product. -/
theorem cornerBlockSpace_annihilated (e : A × C) (he : e * e = e)
    (Λ : (A × C) →ₗ[K] K) (W : Submodule K (A × C))
    (hstab : e ∈ productStabilizer W) (hann : ∀ w ∈ W, Λ w = 0) :
    ∀ w ∈ cornerBlockSpace (K := K) e W, cornerBlockFunctional e he Λ w = 0 := by
  rintro w ⟨x, hx, rfl⟩
  exact hann _ (hstab x hx)

/-- Nondegeneracy on the original first factor restricts to nondegeneracy
on the actual first block factor; no nonzero-block assumption is needed. -/
theorem cornerBlockFunctional_frobenius (e : A × C) (he : e * e = e)
    (Λ : (A × C) →ₗ[K] K)
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0) :
    ∀ a : IdempotentCorner e.1,
      (∀ b : IdempotentCorner e.1, cornerBlockFunctional e he Λ (a * b, 0) = 0) → a = 0 := by
  intro a ha
  have hz : cornerInclusion (K := K) e.1 (congrArg Prod.fst he) a = 0 := by
    apply hFrob
    intro b
    have h := ha (cornerProjection (K := K) e.1 b)
    simp only [cornerBlockFunctional, LinearMap.comp_apply, cornerBlockInclusion,
      LinearMap.prodMap_apply, map_zero] at h
    rw [cornerInclusion_mul, cornerInclusion_projection] at h
    have hm : cornerInclusion (K := K) e.1 (congrArg Prod.fst he) a * (e.1 * b) =
        cornerInclusion (K := K) e.1 (congrArg Prod.fst he) a * b := by
      rw [← mul_assoc, mul_comm _ e.1, cornerInclusion_idempotent_mul]
    exact hm ▸ h
  apply cornerInclusion_injective (K := K) e.1 (congrArg Prod.fst he)
  simpa only [map_zero] using hz

/-- Every actual surjective first projection remains surjective on the
first corner factor after the block quotient map. -/
theorem cornerBlockSpace_fst_surjective (e : A × C) (V : Submodule K (A × C))
    (hV : ∀ b : A, ∃ x ∈ V, x.1 = b) :
    ∀ b : IdempotentCorner e.1, ∃ x ∈ cornerBlockSpace (K := K) e V, x.1 = b := by
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (Ideal.span ({1 - e.1} : Set A)) b
  obtain ⟨x, hx, hxa⟩ := hV a
  refine ⟨cornerBlockProjection (K := K) e x, ⟨x, hx, rfl⟩, ?_⟩
  change cornerProjection (K := K) e.1 x.1 = cornerProjection (K := K) e.1 a
  rw [hxa]

#assert_trust kernel cornerProjection_self
#assert_trust kernel cornerProjection_inclusion
#assert_trust kernel cornerBlockInclusion_injective
#assert_trust kernel cornerBlockSpace_inclusion
#assert_trust kernel submodule_map_list_prod
#assert_trust kernel cornerBlockSpace_annihilated
#assert_trust kernel cornerBlockFunctional_frobenius
#assert_trust kernel cornerBlockSpace_fst_surjective
#print axioms cornerBlockFunctional_frobenius

end
end NLA.Proofs.TR14
