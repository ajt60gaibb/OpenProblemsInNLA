import NLA.Proofs.TR26.FixedDiscriminantResultant

/-! Coefficient-ring specialization of the fixed discriminant. This allows the
actual Wronskian coefficient linear forms to be substituted without changing the
fixed degree or dropping the projective point at infinity. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MvPolynomial
namespace NLA.Proofs.TR26.BinaryDiscriminant

theorem eval₂_fixedDiscriminant {R : Type*} [CommRing R]
    (φ : ℂ →+* R) (k : ℕ) (c : Fin (k + 1) → R) :
    MvPolynomial.eval₂ φ c (fixedDiscriminant k) = (sylvesterMatrix k c).det := by
  change (MvPolynomial.eval₂Hom φ c) (fixedDiscriminant k) = _
  unfold fixedDiscriminant
  rw [(MvPolynomial.eval₂Hom φ c).map_det, map_sylvesterMatrix]
  simp only [eval₂Hom_X']

theorem fixedDiscriminant_aeval_homogeneous {ι : Type*} (k : ℕ)
    (c : Fin (k + 1) → MvPolynomial ι ℂ) (hc : ∀ i, (c i).IsHomogeneous 1) :
    (MvPolynomial.aeval c (fixedDiscriminant k)).IsHomogeneous (2 * k - 2) := by
  simpa only [one_mul] using (fixedDiscriminant_homogeneous k).aeval c hc

theorem eval_specialized_fixedDiscriminant {ι : Type*} (k : ℕ)
    (c : Fin (k + 1) → MvPolynomial ι ℂ) (x : ι → ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval c (fixedDiscriminant k)) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (c i)) (fixedDiscriminant k) := by
  rw [aeval_def, eval_eval₂]
  have hcomp : (MvPolynomial.eval x).comp (algebraMap ℂ (MvPolynomial ι ℂ)) =
      RingHom.id ℂ := by ext r; simp
  rw [hcomp]
  rfl

#assert_trust kernel eval₂_fixedDiscriminant
#assert_trust kernel fixedDiscriminant_aeval_homogeneous
#assert_trust kernel eval_specialized_fixedDiscriminant
#print axioms eval_specialized_fixedDiscriminant
end NLA.Proofs.TR26.BinaryDiscriminant
