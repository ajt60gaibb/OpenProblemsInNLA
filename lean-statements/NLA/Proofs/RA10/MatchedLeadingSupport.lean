import NLA.Proofs.RA10.MatchedLeadingRidge
import NLA.Proofs.RA10.SelectedProjectionFunction

/-! RA-10 selected support algebra for the actual compression `P * A * P`.
This inserts the selected projector in the left resolvent of source Equation (14).
The nuclear ideal estimate and full transfer target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem supportSpectralMatrix_eq_diagonal {n : ℕ}
    (w : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.SpectralMatrix w Q =
      Q * Matrix.diagonal w * Q.transpose := by
  ext i j
  simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem supportSpectralMatrix_commutes {n : ℕ}
    (w v : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQTQ : Q.transpose * Q = 1) :
    NLA.Statements.RA10.SpectralMatrix w Q *
        NLA.Statements.RA10.SpectralMatrix v Q =
      NLA.Statements.RA10.SpectralMatrix v Q *
        NLA.Statements.RA10.SpectralMatrix w Q := by
  simp only [supportSpectralMatrix_eq_diagonal]
  let D := Matrix.diagonal w
  let E := Matrix.diagonal v
  have hDE : D * E = E * D := by
    dsimp [D, E]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    exact mul_comm (w a) (v a)
  calc
    (Q * D * Q.transpose) * (Q * E * Q.transpose) =
        Q * (D * E) * Q.transpose := by
      calc
        (Q * D * Q.transpose) * (Q * E * Q.transpose) =
            Q * D * (Q.transpose * Q) * E * Q.transpose := by
          simp only [Matrix.mul_assoc]
        _ = Q * (D * E) * Q.transpose := by
          rw [hQTQ]
          simp [Matrix.mul_assoc]
    _ = Q * (E * D) * Q.transpose := by rw [hDE]
    _ = (Q * E * Q.transpose) * (Q * D * Q.transpose) := by
      calc
        Q * (E * D) * Q.transpose =
            Q * E * (Q.transpose * Q) * D * Q.transpose := by
          rw [hQTQ]
          simp [Matrix.mul_assoc]
        _ = (Q * E * Q.transpose) * (Q * D * Q.transpose) := by
          simp only [Matrix.mul_assoc]

theorem matchedLeading_supported {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    P * B₀ * P = B₀ := by
  dsimp
  let M := NLA.Statements.RA10.SpectralMatrix eigenvaluesA QAhat
  have hM : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      M eigenvaluesA QAhat := ⟨hA.1, hA.2.1, hAhat.2.2.1, rfl⟩
  have hPMP : selectedProjection k QAhat * M * selectedProjection k QAhat =
      NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat :=
    selectedProjection_functionMatrix (k := k) hM (fun t : ℝ => t)
  have hPP : selectedProjection k QAhat * selectedProjection k QAhat =
      selectedProjection k QAhat := selectedProjection_idempotent (k := k) hAhat
  calc
    selectedProjection k QAhat *
        NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat *
        selectedProjection k QAhat =
        selectedProjection k QAhat *
          (selectedProjection k QAhat * M * selectedProjection k QAhat) *
          selectedProjection k QAhat := by rw [hPMP]
    _ = (selectedProjection k QAhat * selectedProjection k QAhat) * M *
          (selectedProjection k QAhat * selectedProjection k QAhat) := by
      simp only [Matrix.mul_assoc]
    _ = selectedProjection k QAhat * M * selectedProjection k QAhat := by rw [hPP]
    _ = NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t)
        eigenvaluesA QAhat := hPMP

theorem selectedCompression_supported {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    {Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat : Fin n → ℝ}
    {QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let C := P * A * P
    P * C * P = C := by
  dsimp
  have hPP : selectedProjection k QAhat * selectedProjection k QAhat =
      selectedProjection k QAhat := selectedProjection_idempotent (k := k) hAhat
  calc
    selectedProjection k QAhat * (selectedProjection k QAhat * A *
        selectedProjection k QAhat) * selectedProjection k QAhat =
        (selectedProjection k QAhat * selectedProjection k QAhat) * A *
          (selectedProjection k QAhat * selectedProjection k QAhat) := by
      simp only [Matrix.mul_assoc]
    _ = selectedProjection k QAhat * A * selectedProjection k QAhat := by rw [hPP]

theorem matchedLeading_compressionDifference_supported {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    let C := P * A * P
    P * (B₀ - C) * P = B₀ - C := by
  dsimp
  rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [matchedLeading_supported hA hAhat, selectedCompression_supported A hAhat]

theorem matchedLeading_shiftInverse_commutes {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    P * (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹ =
      (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹ * P := by
  dsimp
  let d : Fin n → ℝ := fun a => if a.val < k then 1 else 0
  let r : Fin n → ℝ := fun a => 1 / (s + if a.val < k then eigenvaluesA a else 0)
  have hP : selectedProjection k QAhat =
      NLA.Statements.RA10.SpectralMatrix d QAhat := by
    ext i j
    simp only [selectedProjection, NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a.val < k <;> simp [d, ha]
  have hB0 := matchedLeading_orderedPSD (k := k) hA hAhat
  have hR : (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
      NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ =
      NLA.Statements.RA10.SpectralMatrix r QAhat := by
    have h := (spectralShift_inverse hs hB0).symm
    change _ = NLA.Statements.RA10.SpectralMatrix r QAhat at h ⊢
    exact h
  have hQTQ : QAhat.transpose * QAhat = 1 := by
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      hAhat.2.2.1 a b
  rw [hP, hR]
  exact supportSpectralMatrix_commutes d r QAhat hQTQ

theorem matchedLeading_leftResolvent_restriction {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    let C := P * A * P
    let D := B₀ - C
    let RB := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹
    let RC := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹
    RB * D * RC = (P * RB * P) * D * RC := by
  dsimp
  let P := selectedProjection k QAhat
  let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
  let C := P * A * P
  let D := B₀ - C
  let RB := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹
  let RC := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹
  change RB * D * RC = (P * RB * P) * D * RC
  have hPP : P * P = P := selectedProjection_idempotent (k := k) hAhat
  have hPDP : P * D * P = D :=
    matchedLeading_compressionDifference_supported hA hAhat
  have hPR : P * RB = RB * P := matchedLeading_shiftInverse_commutes hs hA hAhat
  have hPD : P * D = D := by
    calc
      P * D = P * (P * D * P) := by rw [hPDP]
      _ = (P * P) * D * P := by simp only [Matrix.mul_assoc]
      _ = P * D * P := by rw [hPP]
      _ = D := hPDP
  have hPRP : P * RB * P = RB * P := by
    rw [hPR]
    simp only [Matrix.mul_assoc, hPP]
  calc
    RB * D * RC = RB * (P * D) * RC := by rw [hPD]
    _ = (RB * P) * D * RC := by simp only [Matrix.mul_assoc]
    _ = (P * RB * P) * D * RC := by rw [hPRP]

#assert_trust kernel matchedLeading_supported
#assert_trust kernel selectedCompression_supported
#assert_trust kernel matchedLeading_compressionDifference_supported
#assert_trust kernel matchedLeading_shiftInverse_commutes
#assert_trust kernel matchedLeading_leftResolvent_restriction
#print axioms matchedLeading_leftResolvent_restriction

end NLA.Proofs.RA10
