import NLA.Proofs.TR14.GL2CoefficientBasis

/-!
The exact, unweighted moment-vector dual of homogeneous binary forms.
The coefficient of `X^(D-j)Y^j` pairs with `h_j`, with no binomial factor.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open scoped BigOperators
noncomputable section

/-- The exact complex-linear functional specified by all zero-based moments. -/
def homogeneousMoment {D : ℕ} (h : Fin (D + 1) → ℂ) : BinaryMoment D where
  toFun P := ∑ j : Fin (D + 1), h j * ((binaryFormEquiv D).symm P) j
  map_add' P Q := by
    simp [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [RingHom.id_apply]
    ring

/-- Evaluating the functional on `X^(D-j)Y^j` returns the frozen `h_j`. -/
theorem homogeneousMoment_monomial {D : ℕ} (h : Fin (D + 1) → ℂ)
    (j : Fin (D + 1)) :
    homogeneousMoment h (binaryMonomial D j) = h j := by
  simp [homogeneousMoment, binaryFormEquiv_symm_monomial, Pi.single_apply]

theorem momentCoordinates_homogeneousMoment {D : ℕ} (h : Fin (D + 1) → ℂ) :
    momentCoordinates (homogeneousMoment h) = h := by
  funext j
  exact homogeneousMoment_monomial h j

/-- Every complex-linear homogeneous dual is reconstructed from its exact
monomial coordinates. -/
theorem homogeneousMoment_momentCoordinates {D : ℕ} (L : BinaryMoment D) :
    homogeneousMoment (momentCoordinates L) = L := by
  ext P
  let g := (binaryFormEquiv D).symm P
  have hp : P = ∑ j : Fin (D + 1), g j • binaryMonomial D j := by
    calc
      P = binaryFormEquiv D g := ((binaryFormEquiv D).apply_symm_apply P).symm
      _ = _ := binaryFormEquiv_eq_sum D g
  change (∑ j : Fin (D + 1), L (binaryMonomial D j) * g j) = L P
  rw [hp, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The transformed moments are the monomial coordinates of the inverse-dual
functional for the explicit chart substitution. -/
def transformedMoments (z : ℂ) {D : ℕ} (h : Fin (D + 1) → ℂ) :
    Fin (D + 1) → ℂ :=
  momentCoordinates (chartMoment z (homogeneousMoment h))

theorem homogeneousMoment_transformedMoments (z : ℂ) {D : ℕ}
    (h : Fin (D + 1) → ℂ) :
    homogeneousMoment (transformedMoments z h) =
      chartMoment z (homogeneousMoment h) :=
  homogeneousMoment_momentCoordinates _

theorem homogeneousMoment_eq_zero_iff {D : ℕ} (h : Fin (D + 1) → ℂ) :
    homogeneousMoment h = 0 ↔ h = 0 := by
  constructor
  · intro hz
    rw [← momentCoordinates_homogeneousMoment h]
    funext j
    simp [hz, momentCoordinates]
  · intro hz
    subst h
    ext P
    simp [homogeneousMoment]

theorem transformedMoments_eq_zero_iff (z : ℂ) {D : ℕ}
    (h : Fin (D + 1) → ℂ) :
    transformedMoments z h = 0 ↔ h = 0 := by
  rw [← homogeneousMoment_eq_zero_iff (transformedMoments z h),
    homogeneousMoment_transformedMoments]
  constructor
  · intro hz
    apply (homogeneousMoment_eq_zero_iff h).mp
    ext P
    have heval := LinearMap.congr_fun hz ((chartPhiEquiv z D) P)
    simpa [chartMoment] using heval
  · intro hz
    have hL : homogeneousMoment h = 0 := (homogeneousMoment_eq_zero_iff h).mpr hz
    rw [hL]
    ext P
    simp [chartMoment]

#assert_trust kernel homogeneousMoment
#assert_trust kernel homogeneousMoment_monomial
#assert_trust kernel homogeneousMoment_momentCoordinates
#assert_trust kernel homogeneousMoment_transformedMoments
#assert_trust kernel transformedMoments_eq_zero_iff
#print axioms transformedMoments_eq_zero_iff

end
end NLA.Proofs.TR14
