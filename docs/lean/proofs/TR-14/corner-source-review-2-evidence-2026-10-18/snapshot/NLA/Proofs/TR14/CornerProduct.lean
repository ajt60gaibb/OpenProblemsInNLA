import NLA.Proofs.TR14.IdempotentCorner
import Mathlib.RingTheory.Nilpotent.Basic

/-! Actual product decomposition of an idempotent corner and reducedness of
corners of reduced algebras. Zero components remain allowed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

noncomputable section
variable {K A C : Type*} [Field K] [CommRing A] [CommRing C]
  [Algebra K A] [Algebra K C]

/-- The actual corner projection to the two factor corners. -/
def cornerProductMap (e : A × C) :
    IdempotentCorner e →ₐ[K] (IdempotentCorner e.1 × IdempotentCorner e.2) :=
  (cornerMap (K := K) e (AlgHom.fst K A C)).prod
    (cornerMap (K := K) e (AlgHom.snd K A C))

@[simp] theorem cornerProductMap_projection (e x : A × C) :
    cornerProductMap (K := K) e (cornerProjection (K := K) e x) =
      (cornerProjection (K := K) e.1 x.1, cornerProjection (K := K) e.2 x.2) := rfl

/-- This product map is an actual bijection, including zero corners. -/
theorem cornerProductMap_bijective (e : A × C) (he : e * e = e) :
    Function.Bijective (cornerProductMap (K := K) e) := by
  have heA : e.1 * e.1 = e.1 := congrArg Prod.fst he
  have heC : e.2 * e.2 = e.2 := congrArg Prod.snd he
  have hzero (x : IdempotentCorner e) (hx : cornerProductMap (K := K) e x = 0) : x = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective K
      (Ideal.span ({1 - e} : Set (A × C))) x
    apply (cornerProjection_eq_zero_iff (K := K) e he a).mpr
    apply Prod.ext
    · exact (cornerProjection_eq_zero_iff (K := K) e.1 heA a.1).mp (congrArg Prod.fst hx)
    · exact (cornerProjection_eq_zero_iff (K := K) e.2 heC a.2).mp (congrArg Prod.snd hx)
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  · rintro ⟨a, c⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (Ideal.span ({1 - e.1} : Set A)) a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (Ideal.span ({1 - e.2} : Set C)) c
    exact ⟨cornerProjection (K := K) e (x, y), rfl⟩

/-- The product block is genuinely the product of the two actual corners. -/
def cornerProductEquiv (e : A × C) (he : e * e = e) :
    IdempotentCorner e ≃ₐ[K] (IdempotentCorner e.1 × IdempotentCorner e.2) :=
  AlgEquiv.ofBijective (cornerProductMap e) (cornerProductMap_bijective e he)

@[simp] theorem cornerProductEquiv_projection (e x : A × C) (he : e * e = e) :
    cornerProductEquiv (K := K) e he (cornerProjection (K := K) e x) =
      (cornerProjection (K := K) e.1 x.1, cornerProjection (K := K) e.2 x.2) := rfl

/-- The product equivalence agrees exactly with the ambient block inclusion. -/
theorem cornerProductEquiv_inclusion (e : A × C) (he : e * e = e)
    (x : IdempotentCorner e) :
    cornerInclusion (K := K) e he x =
      (cornerInclusion (K := K) e.1 (congrArg Prod.fst he)
          (cornerProductEquiv (K := K) e he x).1,
       cornerInclusion (K := K) e.2 (congrArg Prod.snd he)
          (cornerProductEquiv (K := K) e he x).2) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective K
    (Ideal.span ({1 - e} : Set (A × C))) x
  rfl

variable {B : Type*} [CommRing B] [Algebra K B]

/-- Positive powers are preserved by the ambient inclusion, despite its
identity being the block idempotent rather than the ambient one. -/
theorem cornerInclusion_pow_succ (e : B) (he : e * e = e)
    (x : IdempotentCorner e) (n : ℕ) :
    cornerInclusion (K := K) e he (x ^ (n + 1)) =
      (cornerInclusion (K := K) e he x) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        cornerInclusion (K := K) e he (x ^ ((n + 1) + 1)) =
            cornerInclusion (K := K) e he (x ^ (n + 1)) *
              cornerInclusion (K := K) e he x := by rw [pow_succ, cornerInclusion_mul]
        _ = (cornerInclusion (K := K) e he x) ^ (n + 1) *
              cornerInclusion (K := K) e he x := by rw [ih]
        _ = (cornerInclusion (K := K) e he x) ^ ((n + 1) + 1) := (pow_succ _ _).symm

include K

/-- A corner of an actual reduced algebra is reduced; no reducedness of
arbitrary ambient moment algebras is asserted. -/
theorem corner_isReduced [IsReduced B] (e : B) (he : e * e = e) :
    IsReduced (IdempotentCorner e) := by
  constructor
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have hxn : x ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  have hy : IsNilpotent (cornerInclusion (K := K) e he x) := by
    refine ⟨n + 1, ?_⟩
    rw [← cornerInclusion_pow_succ, hxn, map_zero]
  apply cornerInclusion_injective (K := K) e he
  rw [map_zero]
  exact hy.eq_zero

#assert_trust kernel cornerProductMap
#assert_trust kernel cornerProductMap_bijective
#assert_trust kernel cornerProductEquiv
#assert_trust kernel cornerProductEquiv_inclusion
#assert_trust kernel cornerInclusion_pow_succ
#assert_trust kernel corner_isReduced
#print axioms cornerProductEquiv
#print axioms corner_isReduced

end
end NLA.Proofs.TR14
