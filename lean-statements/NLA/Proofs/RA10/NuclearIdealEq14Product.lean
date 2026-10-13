import NLA.Proofs.RA10.NuclearNormHomogeneity
import NLA.Proofs.RA10.NuclearIdealLeft
import NLA.Proofs.RA10.NuclearIdealRight
import NLA.Proofs.RA10.RidgeResolventOpNormSelected
import NLA.Proofs.RA10.NuclearNormZero

/-! RA-10 source Equation (14): sharp nuclear estimate for the exact
selected-range resolvent product. The restricted ridge difference and
full transfer Target remain separate gates. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

theorem matchedLeading_ridge_nuclear_product_le {n k : ℕ} {s : ℝ}
    (hs : 0 < s) (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    (j : Fin n) (hj : j.val + 1 = k) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    let C := P * A * P
    let RB := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹
    let RC := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹
    NLA.Statements.RA10.NuclearNorm (s • ((P * RB * P) * (B₀ - C) * RC)) ≤
      (1 / (s + eigenvaluesA j)) * NLA.Statements.RA10.NuclearNorm (B₀ - C) := by
  let P := selectedProjection k QAhat
  let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
  let C := P * A * P
  let RB := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹
  let RC := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹
  let X := P * RB * P
  let D := B₀ - C
  change NLA.Statements.RA10.NuclearNorm (s • (X * D * RC)) ≤
    (1 / (s + eigenvaluesA j)) * NLA.Statements.RA10.NuclearNorm D
  have hX : ‖X‖ ≤ 1 / (s + eigenvaluesA j) :=
    matchedLeading_selectedResolvent_opNorm_le hs hk hkn hA hAhat j hj
  have hRC : ‖RC‖ ≤ 1 / s :=
    spectralShift_resolvent_opNorm_le hs hC
  have hsc : 0 < s + eigenvaluesA j := by linarith [hA.1 j]
  have hN : 0 ≤ NLA.Statements.RA10.NuclearNorm D := nuclearNorm_nonneg D
  have hRnn : 0 ≤ ‖RC‖ := norm_nonneg _
  have hAn : 0 ≤ (1 : ℝ) / (s + eigenvaluesA j) :=
    le_of_lt (one_div_pos.mpr hsc)
  have hle :
      NLA.Statements.RA10.NuclearNorm (X * D * RC) ≤
        (‖X‖ * NLA.Statements.RA10.NuclearNorm D) * ‖RC‖ := by
    calc
      NLA.Statements.RA10.NuclearNorm (X * D * RC) ≤
          NLA.Statements.RA10.NuclearNorm (X * D) * ‖RC‖ :=
        nuclearIdeal_right (X * D) RC
      _ ≤ (‖X‖ * NLA.Statements.RA10.NuclearNorm D) * ‖RC‖ :=
        mul_le_mul_of_nonneg_right (nuclearIdeal_left X D) hRnn
  have hbound :
      (‖X‖ * NLA.Statements.RA10.NuclearNorm D) * ‖RC‖ ≤
        (((1 : ℝ) / (s + eigenvaluesA j)) *
          NLA.Statements.RA10.NuclearNorm D) * (1 / s) := by
    calc
      (‖X‖ * NLA.Statements.RA10.NuclearNorm D) * ‖RC‖ ≤
          (((1 : ℝ) / (s + eigenvaluesA j)) *
            NLA.Statements.RA10.NuclearNorm D) * ‖RC‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hX hN) hRnn
      _ ≤ (((1 : ℝ) / (s + eigenvaluesA j)) *
          NLA.Statements.RA10.NuclearNorm D) * (1 / s) :=
        mul_le_mul_of_nonneg_left hRC (mul_nonneg hAn hN)
  rw [nuclearNorm_smul, abs_of_pos hs]
  calc
    s * NLA.Statements.RA10.NuclearNorm (X * D * RC) ≤
        s * ((‖X‖ * NLA.Statements.RA10.NuclearNorm D) * ‖RC‖) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt hs)
    _ ≤ s * ((((1 : ℝ) / (s + eigenvaluesA j)) *
        NLA.Statements.RA10.NuclearNorm D) * (1 / s)) :=
      mul_le_mul_of_nonneg_left hbound (le_of_lt hs)
    _ = (1 / (s + eigenvaluesA j)) *
        NLA.Statements.RA10.NuclearNorm D := by
      have hsne : s ≠ 0 := ne_of_gt hs
      calc
        s * ((((1 : ℝ) / (s + eigenvaluesA j)) *
            NLA.Statements.RA10.NuclearNorm D) * (1 / s)) =
            (((1 : ℝ) / (s + eigenvaluesA j)) *
              NLA.Statements.RA10.NuclearNorm D) * (s * (1 / s)) := by ring
        _ = (1 / (s + eigenvaluesA j)) *
            NLA.Statements.RA10.NuclearNorm D := by simp [hsne]

#assert_trust kernel matchedLeading_ridge_nuclear_product_le
#print axioms matchedLeading_ridge_nuclear_product_le

end NLA.Proofs.RA10
