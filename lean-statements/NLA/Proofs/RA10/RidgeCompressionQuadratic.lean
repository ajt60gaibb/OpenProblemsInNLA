import NLA.Proofs.RA10.RidgeCompressionEnergy
import NLA.Proofs.RA10.HermitianPositivePartOrder
import NLA.Proofs.RA10.SelectedSpectralNuclear
import NLA.Proofs.RA10.RidgeResolventLoewner

/-! A pointwise positive-eigenvector bound for ridge compression. Replacing
the two quadratic forms by their positive parts permits summation over a full
orthonormal basis, avoiding a separate positive-eigenspace variational proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix
open NLA.Statements.RA10
open scoped BigOperators

namespace NLA.Proofs.RA10

theorem ridgeFunctionMatrix_posSemidef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a Q) {s : ℝ} (hs : 0 < s) :
    (FunctionMatrix (ridgeAtom s) a Q).PosSemidef := by
  change (SpectralMatrix (fun i => ridgeAtom s (a i)) Q).PosSemidef
  rw [spectralMatrix_factor]
  have hd : (diagonal (fun i => ridgeAtom s (a i))).PosSemidef :=
    PosSemidef.diagonal (fun i => div_nonneg (hA.1 i) (by linarith [hA.1 i]))
  simpa only [conjTranspose_eq_transpose_of_trivial] using hd.mul_mul_conjTranspose_same Q

theorem one_sub_ridgeFunctionMatrix_posSemidef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a Q) {s : ℝ} (hs : 0 < s) :
    (1 - FunctionMatrix (ridgeAtom s) a Q).PosSemidef := by
  rw [ridgeFunctionMatrix_eq_resolvent hs hA, sub_sub_cancel]
  exact ((sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mp
    (spectralShift_resolvent_nonnegative hs hA)).smul hs.le

theorem ridgeDifference_eigenvalue_le_one {n : ℕ}
    {A C : Matrix (Fin n) (Fin n) ℝ} {a h : Fin n → ℝ}
    {QA QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a QA)
    (hC : OrderedPSDSpectralDecomposition C h QC)
    {s ℓ : ℝ} (hs : 0 < s) (v : Fin n → ℝ) (hv : v ⬝ᵥ v = 1)
    (heig : (FunctionMatrix (ridgeAtom s) h QC -
      FunctionMatrix (ridgeAtom s) a QA) *ᵥ v = ℓ • v) : ℓ ≤ 1 := by
  have hp := (one_sub_ridgeFunctionMatrix_posSemidef hC hs).add
    (ridgeFunctionMatrix_posSemidef hA hs)
  have heq : 1 - FunctionMatrix (ridgeAtom s) h QC + FunctionMatrix (ridgeAtom s) a QA =
      1 - (FunctionMatrix (ridgeAtom s) h QC - FunctionMatrix (ridgeAtom s) a QA) := by abel
  rw [heq] at hp
  have h := hp.dotProduct_mulVec_nonneg v
  simp only [star_trivial, sub_mulVec, one_mulVec, heig, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, hv, mul_one] at h
  linarith

private theorem ridgeCompression_scalar_bound
    {s c ℓ μ U H D T Δ : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
    (hμ : 0 ≤ μ) (hμ1 : μ < 1) (hrel : ℓ * (1 - μ) = μ)
    (hU : 0 ≤ U) (hmass : 1 ≤ 2 * (1 - μ) * U)
    (hD : D = μ * s + μ * (2 - μ) * H)
    (hH : c * U ≤ H + Δ) (hDT : D ≤ T) (hΔ : 0 ≤ Δ) :
    ℓ * (s + c) / 2 ≤ T + Δ := by
  have hμlower : ℓ / 2 ≤ μ := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hmass hℓ.le
  have hrelU := congrArg (fun x => x * U) hrel
  have hmassμ : ℓ / 2 ≤ μ * U := by nlinarith
  have hcoeff : 0 ≤ μ * (2 - μ) := mul_nonneg hμ (by linarith)
  have hcoeff1 : μ * (2 - μ) ≤ 1 := by nlinarith [sq_nonneg (1 - μ)]
  have hmasscoeff : ℓ / 2 ≤ μ * (2 - μ) * U := by
    nlinarith [mul_nonneg (mul_nonneg hμ (by linarith : 0 ≤ 1 - μ)) hU]
  have hHscaled := mul_le_mul_of_nonneg_left hH hcoeff
  have hUscaled := mul_le_mul_of_nonneg_left hmasscoeff hc.le
  have hsscaled := mul_le_mul_of_nonneg_left hμlower hs.le
  have hΔscaled := mul_le_mul_of_nonneg_right hcoeff1 hΔ
  nlinarith

/-- Source (7) with the defect and difference replaced by positive parts.
The conclusion is designed to sum over every vector in an eigenbasis. -/
theorem ridgeCompression_eigenvector_bound {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.transpose = P) (hPP : P * P = P)
    {a h : Fin n → ℝ} {QA QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : OrderedPSDSpectralDecomposition A a QA)
    (hC : OrderedPSDSpectralDecomposition (P * A * P) h QC)
    {s c ℓ : ℝ} (hs : 0 < s) (hc : 0 < c) (hℓ : 0 < ℓ)
    (v : Fin n → ℝ) (hunit : v ⬝ᵥ v = 1)
    (heig : (FunctionMatrix (ridgeAtom s) h QC -
      FunctionMatrix (ridgeAtom s) a QA) *ᵥ v = ℓ • v) :
    ℓ * (s + c) / 2 ≤
      v ⬝ᵥ ((hermitianPositivePart (P * A * P - A) +
        hermitianPositivePart (c • P - P * A * P)) *ᵥ v) := by
  let C := P * A * P
  let u := P *ᵥ v
  let w := v - u
  let μ := ℓ / (1 + ℓ)
  have hden : 0 < 1 + ℓ := by linarith
  have hμ : 0 < μ := div_pos hℓ hden
  have hμ1 : μ < 1 := by dsimp [μ]; apply (div_lt_one hden).mpr; linarith
  have hrel : ℓ * (1 - μ) = μ := by dsimp [μ]; field_simp [ne_of_gt hden]; ring
  have hApsd := (sourcePositiveSemidefinite_iff_mathlibPosSemidef A).mp
    (orderedPSDSpectralDecomposition_positiveSemidefinite hA)
  have hCpsd := (sourcePositiveSemidefinite_iff_mathlibPosSemidef C).mp
    (orderedPSDSpectralDecomposition_positiveSemidefinite hC)
  have hAt : A.transpose = A := Matrix.isHermitian_iff_isSymm.mp hApsd.1
  have hPu : P *ᵥ u = u := by dsimp [u]; rw [mulVec_mulVec, hPP]
  have hPvnorm : v ⬝ᵥ u = u ⬝ᵥ u := by
    calc
      v ⬝ᵥ u = v ⬝ᵥ (P *ᵥ u) := by rw [hPu]
      _ = u ⬝ᵥ u := by rw [symmetric_dotProduct_move P hP]
  have hvsplit : v = u + w := by dsimp [w]; abel
  have huw : u ⬝ᵥ w = 0 := by
    dsimp [w]
    rw [dotProduct_sub, dotProduct_comm u v, hPvnorm, sub_self]
  have hwu : w ⬝ᵥ u = 0 := by rw [dotProduct_comm, huw]
  have hnorm : (u ⬝ᵥ u) + (w ⬝ᵥ w) = 1 := by
    have hunit' := hunit
    rw [hvsplit, add_dotProduct, dotProduct_add, dotProduct_add, huw, hwu] at hunit'
    simpa using hunit'
  have henergy := ridgeCompression_eigenvector_energy P hP hPP hA hC hs hℓ v heig
  change u ⬝ᵥ (A *ᵥ w) = -μ * (s * (u ⬝ᵥ u) + u ⬝ᵥ (A *ᵥ u)) ∧
    w ⬝ᵥ (A *ᵥ w) = μ * s * ((u ⬝ᵥ u) - (w ⬝ᵥ w)) +
      μ ^ 2 * (u ⬝ᵥ (A *ᵥ u)) at henergy
  have hmass := ridgeCompression_complement_mass_le hApsd u w hs hμ henergy.1 henergy.2
  have hvCv : v ⬝ᵥ (C *ᵥ v) = u ⬝ᵥ (A *ᵥ u) := by
    dsimp [C, u]
    rw [← mulVec_mulVec, ← mulVec_mulVec, symmetric_dotProduct_move P hP]
  have hcrosssym : w ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ w) := by
    rw [symmetric_dotProduct_move A hAt, dotProduct_comm]
  have hvAv : v ⬝ᵥ (A *ᵥ v) =
      u ⬝ᵥ (A *ᵥ u) + 2 * (u ⬝ᵥ (A *ᵥ w)) + w ⬝ᵥ (A *ᵥ w) := by
    calc
      v ⬝ᵥ (A *ᵥ v) = (u + w) ⬝ᵥ (A *ᵥ (u + w)) := by rw [← hvsplit]
      _ = _ := by rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hcrosssym]; ring
  have hD : v ⬝ᵥ ((C - A) *ᵥ v) = μ * s + μ * (2 - μ) * (u ⬝ᵥ (A *ᵥ u)) := by
    rw [sub_mulVec, dotProduct_sub, hvCv, hvAv, henergy.1, henergy.2]
    nlinarith [congrArg (fun x => μ * s * x) hnorm]
  have hM : (c • P - C).IsHermitian :=
    ((Matrix.isHermitian_iff_isSymm.mpr hP).smul (by rfl)).sub hCpsd.1
  have hDT := (hermitianPositivePart_sub_posSemidef (C - A)
    (hCpsd.1.sub hApsd.1)).dotProduct_mulVec_nonneg v
  simp only [star_trivial, sub_mulVec, dotProduct_sub] at hDT
  have hH := (hermitianPositivePart_sub_posSemidef (c • P - C) hM).dotProduct_mulVec_nonneg v
  simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, hvCv] at hH
  change 0 ≤ v ⬝ᵥ (hermitianPositivePart (c • P - C) *ᵥ v) -
    (c * (v ⬝ᵥ u) - u ⬝ᵥ (A *ᵥ u)) at hH
  rw [hPvnorm] at hH
  have hΔ := (hermitianPositivePart_posSemidef (c • P - C) hM).dotProduct_mulVec_nonneg v
  simp only [star_trivial] at hΔ
  have hU : 0 ≤ u ⬝ᵥ u := by
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))
  change ℓ * (s + c) / 2 ≤
    v ⬝ᵥ ((hermitianPositivePart (C - A) + hermitianPositivePart (c • P - C)) *ᵥ v)
  rw [add_mulVec, dotProduct_add]
  exact ridgeCompression_scalar_bound hs hc hℓ
    (ridgeDifference_eigenvalue_le_one hA hC hs v hunit heig) hμ.le hμ1 hrel hU
    (by nlinarith) hD (by linarith) (by rw [sub_mulVec, dotProduct_sub]; linarith) hΔ

#assert_trust kernel ridgeFunctionMatrix_posSemidef
#assert_trust kernel one_sub_ridgeFunctionMatrix_posSemidef
#assert_trust kernel ridgeDifference_eigenvalue_le_one
#assert_trust kernel ridgeCompression_eigenvector_bound
#print axioms ridgeCompression_eigenvector_bound

end NLA.Proofs.RA10
