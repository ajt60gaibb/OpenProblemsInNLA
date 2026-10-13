import NLA.Proofs.RA10.RidgeCompressionMass
import NLA.Proofs.RA10.RidgeResolventProduct
import Mathlib.Tactic.NoncommRing

/-! Ridge compression energy equations. The auxiliary-vector formulation
clears the shifted resolvents without ever inverting the compression itself. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix
open scoped BigOperators

namespace NLA.Proofs.RA10

theorem symmetric_dotProduct_move {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.transpose = M)
    (x y : Fin n → ℝ) : x ⬝ᵥ (M *ᵥ y) = (M *ᵥ x) ⬝ᵥ y := by
  calc
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
      simpa only [hM] using Matrix.dotProduct_transpose_mulVec M x y
    _ = (M *ᵥ x) ⬝ᵥ y := dotProduct_comm _ _

/-- Source (2) and (4), in global coordinates, from two shifted equations. -/
theorem ridgeCompression_energy_of_shiftEquations {n : ℕ}
    (A P : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose = A) (hP : P.transpose = P) (hPP : P * P = P)
    (v z : Fin n → ℝ) {s μ : ℝ} (hs : 0 < s)
    (hz : s • z + (P * A * P) *ᵥ z = s • v)
    (hv : s • ((1 - μ) • z + μ • v) + A *ᵥ ((1 - μ) • z + μ • v) =
      (s * (1 - μ)) • v) :
    let u := P *ᵥ v
    let w := v - u
    u ⬝ᵥ (A *ᵥ w) = -μ * (s * (u ⬝ᵥ u) + u ⬝ᵥ (A *ᵥ u)) ∧
    w ⬝ᵥ (A *ᵥ w) =
      μ * s * ((u ⬝ᵥ u) - (w ⬝ᵥ w)) + μ ^ 2 * (u ⬝ᵥ (A *ᵥ u)) := by
  let C := P * A * P
  let u := P *ᵥ v
  let w := v - u
  let t := P *ᵥ z
  change u ⬝ᵥ (A *ᵥ w) = _ ∧ w ⬝ᵥ (A *ᵥ w) = _
  change s • z + C *ᵥ z = s • v at hz
  have hPC : P * C = C := by
    dsimp [C]
    rw [← mul_assoc, ← mul_assoc, hPP]
  have hCP : C * P = C := by
    dsimp [C]
    rw [mul_assoc, hPP]
  have hC : C.transpose = C := by simp [C, transpose_mul, hA, hP, mul_assoc]
  have hPu : P *ᵥ u = u := by dsimp [u]; rw [mulVec_mulVec, hPP]
  have hPt : P *ᵥ t = t := by dsimp [t]; rw [mulVec_mulVec, hPP]
  have hPw : P *ᵥ w = 0 := by simp [w, mulVec_sub, hPu, u]
  have hCt : C *ᵥ t = C *ᵥ z := by dsimp [t]; rw [mulVec_mulVec, hCP]
  have hshift : s • t + C *ᵥ z = s • u := by
    have hp := congrArg (fun q => P *ᵥ q) hz
    simpa only [mulVec_add, mulVec_smul, mulVec_mulVec, hPC] using hp
  have hzsplit : z = t + w := by
    ext i
    have hzi := congrFun hz i
    have hpi := congrFun hshift i
    change z i = t i + (v i - u i)
    change s * z i + (C *ᵥ z) i = s * v i at hzi
    change s * t i + (C *ᵥ z) i = s * u i at hpi
    nlinarith
  have hvsplit : v = u + w := by dsimp [w]; abel
  have hPAt : P *ᵥ (A *ᵥ t) = C *ᵥ z := by
    dsimp [t, C]
    simp only [mulVec_mulVec, mul_assoc]
  have hCu : C *ᵥ u = P *ᵥ (A *ᵥ u) := by
    dsimp [C]
    rw [← mulVec_mulVec, hPu, ← mulVec_mulVec]
  have hPAz : P *ᵥ (A *ᵥ z) = C *ᵥ z + P *ᵥ (A *ᵥ w) := by
    calc
      P *ᵥ (A *ᵥ z) = P *ᵥ (A *ᵥ (t + w)) := by rw [← hzsplit]
      _ = C *ᵥ z + P *ᵥ (A *ᵥ w) := by rw [mulVec_add, mulVec_add, hPAt]
  have hPAv : P *ᵥ (A *ᵥ v) = C *ᵥ u + P *ᵥ (A *ᵥ w) := by
    calc
      P *ᵥ (A *ᵥ v) = P *ᵥ (A *ᵥ (u + w)) := by rw [← hvsplit]
      _ = C *ᵥ u + P *ᵥ (A *ᵥ w) := by rw [mulVec_add, mulVec_add, ← hCu]
  have hcrossVec : P *ᵥ (A *ᵥ w) = -μ • (s • u + C *ᵥ u) := by
    have hp := congrArg (fun q => P *ᵥ q) hv
    simp only [mulVec_add, mulVec_smul] at hp
    rw [hPAz, hPAv] at hp
    ext i
    have hpi := congrFun hp i
    have hsi := congrFun hshift i
    change s * ((1 - μ) * t i + μ * u i) +
      ((1 - μ) * ((C *ᵥ z) i + (P *ᵥ (A *ᵥ w)) i) +
        μ * ((C *ᵥ u) i + (P *ᵥ (A *ᵥ w)) i)) = s * (1 - μ) * u i at hpi
    change s * t i + (C *ᵥ z) i = s * u i at hsi
    change (P *ᵥ (A *ᵥ w)) i = -μ * (s * u i + (C *ᵥ u) i)
    linear_combination hpi - (1 - μ) * hsi
  have hcross : u ⬝ᵥ (A *ᵥ w) = -μ * (s * (u ⬝ᵥ u) + u ⬝ᵥ (A *ᵥ u)) := by
    have huC : u ⬝ᵥ (C *ᵥ u) = u ⬝ᵥ (A *ᵥ u) := by
      rw [hCu, symmetric_dotProduct_move P hP, hPu]
    calc
      u ⬝ᵥ (A *ᵥ w) = u ⬝ᵥ (P *ᵥ (A *ᵥ w)) := by
        rw [symmetric_dotProduct_move P hP, hPu]
      _ = -μ * (s * (u ⬝ᵥ u) + u ⬝ᵥ (A *ᵥ u)) := by
        rw [hcrossVec, dotProduct_smul, dotProduct_add, dotProduct_smul, huC]
        rfl
  have hwP (q : Fin n → ℝ) : w ⬝ᵥ (P *ᵥ q) = 0 := by
    rw [symmetric_dotProduct_move P hP, hPw, zero_dotProduct]
  have hwu : w ⬝ᵥ u = 0 := hwP v
  have hwt : w ⬝ᵥ t = 0 := hwP z
  have hwz : w ⬝ᵥ z = w ⬝ᵥ w := by rw [hzsplit, dotProduct_add, hwt, zero_add]
  have hwv : w ⬝ᵥ v = w ⬝ᵥ w := by rw [hvsplit, dotProduct_add, hwu, zero_add]
  have hAt : w ⬝ᵥ (A *ᵥ t) = -μ * s * (u ⬝ᵥ u) := by
    have htenergy := congrArg (fun q => q ⬝ᵥ u) hshift
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at htenergy
    have htuC : t ⬝ᵥ (C *ᵥ u) = (C *ᵥ z) ⬝ᵥ u := by
      rw [symmetric_dotProduct_move C hC, hCt]
    have htAw : t ⬝ᵥ (A *ᵥ w) = t ⬝ᵥ (P *ᵥ (A *ᵥ w)) := by
      rw [symmetric_dotProduct_move P hP, hPt]
    rw [symmetric_dotProduct_move A hA, dotProduct_comm, htAw, hcrossVec,
      dotProduct_smul, dotProduct_add, dotProduct_smul, htuC]
    change -μ * (s * (t ⬝ᵥ u) + (C *ᵥ z) ⬝ᵥ u) = _
    rw [htenergy]
    ring
  have hwAu : w ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ w) := by
    rw [symmetric_dotProduct_move A hA, dotProduct_comm]
  have hwAz : w ⬝ᵥ (A *ᵥ z) = -μ * s * (u ⬝ᵥ u) + w ⬝ᵥ (A *ᵥ w) := by
    calc
      w ⬝ᵥ (A *ᵥ z) = w ⬝ᵥ (A *ᵥ (t + w)) := by rw [← hzsplit]
      _ = _ := by rw [mulVec_add, dotProduct_add, hAt]
  have hwAv : w ⬝ᵥ (A *ᵥ v) = u ⬝ᵥ (A *ᵥ w) + w ⬝ᵥ (A *ᵥ w) := by
    calc
      w ⬝ᵥ (A *ᵥ v) = w ⬝ᵥ (A *ᵥ (u + w)) := by rw [← hvsplit]
      _ = _ := by rw [mulVec_add, dotProduct_add, hwAu]
  refine ⟨hcross, ?_⟩
  have hb := congrArg (fun q => w ⬝ᵥ q) hv
  simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
    smul_eq_mul, hwz, hwv, hwAz, hwAv, hcross] at hb
  nlinarith

/-- The block-energy equations for an actual positive eigenvector of the ridge
difference. Only positive shifts are inverted, so singular compression is included. -/
theorem ridgeCompression_eigenvector_energy {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.transpose = P) (hPP : P * P = P)
    {a h : Fin n → ℝ} {QA QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A a QA)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition (P * A * P) h QC)
    {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 < ℓ) (v : Fin n → ℝ)
    (heig : (NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) h QC -
      NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) a QA) *ᵥ v = ℓ • v) :
    let μ := ℓ / (1 + ℓ)
    let u := P *ᵥ v
    let w := v - u
    u ⬝ᵥ (A *ᵥ w) = -μ * (s * (u ⬝ᵥ u) + u ⬝ᵥ (A *ᵥ u)) ∧
    w ⬝ᵥ (A *ᵥ w) =
      μ * s * ((u ⬝ᵥ u) - (w ⬝ᵥ w)) + μ ^ 2 * (u ⬝ᵥ (A *ᵥ u)) := by
  let C := P * A * P
  let SA := s • (1 : Matrix (Fin n) (Fin n) ℝ) + A
  let SC := s • (1 : Matrix (Fin n) (Fin n) ℝ) + C
  let μ := ℓ / (1 + ℓ)
  let z := s • (SC⁻¹ *ᵥ v)
  have hSA : SA * SA⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (spectralShift_isUnit hs hA))
  have hSC : SC * SC⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (spectralShift_isUnit hs hC))
  have hz : s • z + C *ᵥ z = s • v := by
    calc
      s • z + C *ᵥ z = SC *ᵥ z := by simp [SC, add_mulVec, smul_mulVec]
      _ = s • v := by dsimp [z]; rw [mulVec_smul, mulVec_mulVec, hSC, one_mulVec]
  rw [ridgeFunctionMatrix_sub hs hA hC] at heig
  simp only [smul_mulVec, sub_mulVec, smul_sub] at heig
  change s • (SA⁻¹ *ᵥ v) - z = ℓ • v at heig
  have hsum : z + ℓ • v = s • (SA⁻¹ *ᵥ v) := by
    rw [sub_eq_iff_eq_add.mp heig]
    abel
  have hμrel : (1 - μ) * ℓ = μ := by
    dsimp [μ]
    field_simp [ne_of_gt (show 0 < 1 + ℓ by linarith)]
    ring
  have hvector : (1 - μ) • z + μ • v = (1 - μ) • (s • (SA⁻¹ *ᵥ v)) := by
    rw [← hsum, smul_add]
    simp only [smul_smul, hμrel]
  have hv : s • ((1 - μ) • z + μ • v) + A *ᵥ ((1 - μ) • z + μ • v) =
      (s * (1 - μ)) • v := by
    calc
      s • ((1 - μ) • z + μ • v) + A *ᵥ ((1 - μ) • z + μ • v) =
          SA *ᵥ ((1 - μ) • z + μ • v) := by simp [SA, add_mulVec, smul_mulVec]
      _ = (s * (1 - μ)) • v := by
        rw [hvector, mulVec_smul, mulVec_smul, mulVec_mulVec, hSA, one_mulVec]
        module
  have hApsd := (sourcePositiveSemidefinite_iff_mathlibPosSemidef A).mp
    (orderedPSDSpectralDecomposition_positiveSemidefinite hA)
  exact ridgeCompression_energy_of_shiftEquations A P
    (Matrix.isHermitian_iff_isSymm.mp hApsd.1) hP hPP v z hs hz hv

#assert_trust kernel symmetric_dotProduct_move
#assert_trust kernel ridgeCompression_energy_of_shiftEquations
#assert_trust kernel ridgeCompression_eigenvector_energy
#print axioms ridgeCompression_energy_of_shiftEquations
#print axioms ridgeCompression_eigenvector_energy

end NLA.Proofs.RA10
