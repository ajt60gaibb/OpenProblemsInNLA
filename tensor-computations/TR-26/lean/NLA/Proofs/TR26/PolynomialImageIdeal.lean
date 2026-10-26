import NLA.Statements.TR26
import Mathlib.RingTheory.Nullstellensatz

/-! Vanishing ideals of polynomial images of principal open sets. The
nonzero-image restriction is handled by a genuine nonzero output coordinate.
No dominance or irreducibility hypothesis is assumed for TR-26 here. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
universe u v
namespace NLA.Proofs.TR26
open MvPolynomial

theorem mvPolynomial_eq_zero_of_vanishing_principalOpen
    {τ : Type v} (D f : MvPolynomial τ ℂ) (hD : D ≠ 0)
    (hf : ∀ y : τ → ℂ, MvPolynomial.eval y D ≠ 0 → MvPolynomial.eval y f = 0) :
    f = 0 := by
  have hprod : f*D=0 := by
    apply MvPolynomial.funext
    intro y
    simp only [map_mul,map_zero]
    by_cases hy : MvPolynomial.eval y D = 0
    · rw [hy,mul_zero]
    · rw [hf y hy,zero_mul]
  exact (mul_eq_zero.mp hprod).resolve_right hD

def polynomialImageCoordinates {σ : Type u} {τ : Type v}
    (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ) (y : τ → ℂ) : σ → ℂ :=
  fun i => MvPolynomial.eval y (Φ (MvPolynomial.X i))

theorem eval_polynomialImageCoordinates {σ : Type u} {τ : Type v}
    (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ)
    (y : τ → ℂ) (f : MvPolynomial σ ℂ) :
    MvPolynomial.eval (polynomialImageCoordinates Φ y) f = MvPolynomial.eval y (Φ f) := by
  have hh : (MvPolynomial.aeval y).comp Φ =
      MvPolynomial.aeval (polynomialImageCoordinates Φ y) := by
    ext i
    simp [polynomialImageCoordinates]
  have he := congrArg (fun F : MvPolynomial σ ℂ →ₐ[ℂ] ℂ => F f) hh
  exact he.symm

def principalOpenPolynomialImage {σ : Type u} {τ : Type v}
    (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ) (D : MvPolynomial τ ℂ) :
    Set (σ → ℂ) :=
  {x | ∃ y : τ → ℂ, MvPolynomial.eval y D ≠ 0 ∧
    polynomialImageCoordinates Φ y ≠ 0 ∧ x = polynomialImageCoordinates Φ y}

theorem vanishingIdeal_principalOpenPolynomialImage_eq_ker
    {σ : Type u} {τ : Type v}
    (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ) (D : MvPolynomial τ ℂ)
    (hD : D ≠ 0) (i : σ) (hi : Φ (MvPolynomial.X i) ≠ 0) :
    MvPolynomial.vanishingIdeal ℂ (principalOpenPolynomialImage Φ D) =
      RingHom.ker Φ.toRingHom := by
  ext f
  constructor
  · intro hf
    change Φ f = 0
    have hprod : Φ f * Φ (MvPolynomial.X i) = 0 := by
      apply mvPolynomial_eq_zero_of_vanishing_principalOpen D _ hD
      intro y hyD
      rw [map_mul]
      by_cases hy : polynomialImageCoordinates Φ y = 0
      · have hi0 := congrFun hy i
        change MvPolynomial.eval y (Φ (MvPolynomial.X i)) = 0 at hi0
        rw [hi0,mul_zero]
      · have he := hf (polynomialImageCoordinates Φ y) ⟨y,hyD,hy,rfl⟩
        change MvPolynomial.eval (polynomialImageCoordinates Φ y) f = 0 at he
        rw [eval_polynomialImageCoordinates] at he
        rw [he,zero_mul]
    exact (mul_eq_zero.mp hprod).resolve_right hi
  · intro hf x hx
    rcases hx with ⟨y,_,_,rfl⟩
    change MvPolynomial.eval (polynomialImageCoordinates Φ y) f = 0
    rw [eval_polynomialImageCoordinates]
    change Φ f = 0 at hf
    rw [hf,map_zero]

theorem vanishingIdeal_principalOpenPolynomialImage_isPrime
    {σ : Type u} {τ : Type v}
    (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ) (D : MvPolynomial τ ℂ)
    (hD : D ≠ 0) (i : σ) (hi : Φ (MvPolynomial.X i) ≠ 0) :
    (MvPolynomial.vanishingIdeal ℂ (principalOpenPolynomialImage Φ D)).IsPrime := by
  rw [vanishingIdeal_principalOpenPolynomialImage_eq_ker Φ D hD i hi]
  exact RingHom.ker_isPrime Φ.toRingHom

theorem vanishingIdeal_principalOpenPolynomialImage_mul
    {σ : Type u} {τ : Type v}
    (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ) (D E : MvPolynomial τ ℂ)
    (hD : D ≠ 0) (hE : E ≠ 0) (i : σ) (hi : Φ (MvPolynomial.X i) ≠ 0) :
    MvPolynomial.vanishingIdeal ℂ (principalOpenPolynomialImage Φ (D*E)) =
      MvPolynomial.vanishingIdeal ℂ (principalOpenPolynomialImage Φ D) := by
  rw [vanishingIdeal_principalOpenPolynomialImage_eq_ker Φ (D*E) (mul_ne_zero hD hE) i hi,
    vanishingIdeal_principalOpenPolynomialImage_eq_ker Φ D hD i hi]

#assert_trust kernel mvPolynomial_eq_zero_of_vanishing_principalOpen
#assert_trust kernel eval_polynomialImageCoordinates
#assert_trust kernel vanishingIdeal_principalOpenPolynomialImage_eq_ker
#assert_trust kernel vanishingIdeal_principalOpenPolynomialImage_isPrime
#assert_trust kernel vanishingIdeal_principalOpenPolynomialImage_mul
#print axioms vanishingIdeal_principalOpenPolynomialImage_isPrime
end NLA.Proofs.TR26
