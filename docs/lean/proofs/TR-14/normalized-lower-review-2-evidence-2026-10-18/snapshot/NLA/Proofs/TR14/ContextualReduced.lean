import NLA.Proofs.TR14.ProductStabilizer
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Algebra.Prod

/-! The nilpotent exclusion in the contextual product argument of TR-14,
solution.tex Section 4. Every auxiliary algebra is proved reduced from the
actual Frobenius constraint and all-but-one projection, rather than assuming
that all subalgebras of a nonreduced ambient algebra form a finite set. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

variable {K A C : Type*} [Field K] [CommRing A] [CommRing C]
  [Algebra K A] [Algebra K C] [IsReduced C]

/-- A Frobenius functional and the full first-factor projection exclude a
nilpotent whose translated products lie in an annihilated subspace. -/
theorem nilpotent_eq_zero_of_context
    (Λ : (A × C) →ₗ[K] K) (Q W : Submodule K (A × C))
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0)
    (hQ : ∀ b : A, ∃ x ∈ Q, x.1 = b)
    (hann : ∀ w ∈ W, Λ w = 0)
    (a z : A × C) (ha : IsUnit a.1) (hz : IsNilpotent z)
    (hpres : ∀ x ∈ Q, z * a * x ∈ W) : z = 0 := by
  have hzC : z.2 = 0 := (hz.map (RingHom.snd A C)).eq_zero
  have hzA : z.1 * a.1 = 0 := hFrob _ (by
    intro b
    obtain ⟨x, hx, hxb⟩ := hQ b
    have h := hann _ (hpres x hx)
    have heq : z * a * x = (z.1 * a.1 * b, 0) := by
      apply Prod.ext <;> simp [hzC, hxb]
    exact heq ▸ h)
  apply Prod.ext
  · exact ha.mul_left_eq_zero.mp hzA
  · exact hzC

/-- The preceding exclusion gives reducedness of an actual subalgebra. -/
theorem subalgebra_isReduced_of_context
    (Λ : (A × C) →ₗ[K] K) (Q W : Submodule K (A × C))
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0)
    (hQ : ∀ b : A, ∃ x ∈ Q, x.1 = b)
    (hann : ∀ w ∈ W, Λ w = 0)
    (a : A × C) (ha : IsUnit a.1) (S : Subalgebra K (A × C))
    (hpres : ∀ z ∈ S, ∀ x ∈ Q, z * a * x ∈ W) : IsReduced S := by
  constructor
  intro z hz
  apply Subtype.ext
  exact nilpotent_eq_zero_of_context Λ Q W hFrob hQ hann a z ha
    (hz.map S.val) (hpres z z.property)

/-- In particular, the stabilizer of the full product is reduced. -/
theorem productStabilizer_isReduced_of_context
    (Λ : (A × C) →ₗ[K] K) (W : Submodule K (A × C))
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0)
    (hW : ∀ b : A, ∃ x ∈ W, x.1 = b)
    (hann : ∀ w ∈ W, Λ w = 0) : IsReduced (productStabilizer W) := by
  apply subalgebra_isReduced_of_context Λ W W hFrob hW hann 1 (by simp)
  intro z hz x hx
  simpa only [mul_one] using hz x hx

/-- The transformation lemma's actual `K,T` data satisfy the exclusion for
all products of the other factors. This proves every auxiliary `K` reduced. -/
theorem auxiliarySubalgebra_isReduced_of_context
    (Λ : (A × C) →ₗ[K] K) (V Q T W : Submodule K (A × C))
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0)
    (hQ : ∀ b : A, ∃ x ∈ V * Q, x.1 = b)
    (hann : ∀ w ∈ W, Λ w = 0)
    (a : A × C) (ha : IsUnit a.1) (S : Subalgebra K (A × C))
    (hST : S.toSubmodule * T ≤ T)
    (haV : ∀ v ∈ V, a * v ∈ T)
    (hTQ : T * Q ≤ W) : IsReduced S := by
  apply subalgebra_isReduced_of_context Λ (V * Q) W hFrob hQ hann a ha S
  intro z hz x hx
  refine Submodule.mul_induction_on hx (fun v hv q hq => ?_) (fun x y hx hy => ?_)
  · have hzat : z * (a * v) ∈ T :=
      hST (Submodule.mul_mem_mul hz (haV v hv))
    have hprod := hTQ (Submodule.mul_mem_mul hzat hq)
    simpa only [mul_assoc] using hprod
  · simpa only [mul_add] using W.add_mem hx hy

#assert_trust kernel nilpotent_eq_zero_of_context
#assert_trust kernel auxiliarySubalgebra_isReduced_of_context
#assert_trust kernel productStabilizer_isReduced_of_context
#print axioms nilpotent_eq_zero_of_context
#print axioms auxiliarySubalgebra_isReduced_of_context

end NLA.Proofs.TR14
