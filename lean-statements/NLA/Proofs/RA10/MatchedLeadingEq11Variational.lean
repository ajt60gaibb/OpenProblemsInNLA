import NLA.Proofs.RA10.MatchedLeadingEq11Scalar
import NLA.Proofs.RA10.HermitianPositivePart
import NLA.Proofs.RA10.SelectedCompressionEigenvalue
import NLA.Proofs.RA10.CustomPSDMathlibBridge
import Mathlib.Tactic.NoncommRing

/-! RA-10 source Equation (11): coefficient-one matrix positive-part bridge
for the actual selected compression. The frozen full Target remains open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

private theorem orthogonalProjection_posSemidef {n : ℕ}
    (R : Matrix (Fin n) (Fin n) ℝ)
    (hRt : R.transpose = R) (hRR : R * R = R) :
    Matrix.PosSemidef R := by
  have hone : Matrix.PosSemidef (1 : Matrix (Fin n) (Fin n) ℝ) :=
    Matrix.PosSemidef.one
  have hgram := hone.conjTranspose_mul_mul_same R
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
    hRt, mul_one, hRR] using hgram

private theorem trace_mul_orthogonalProjection_le {n : ℕ}
    (R T : Matrix (Fin n) (Fin n) ℝ)
    (hRt : R.transpose = R) (hRR : R * R = R)
    (hT : Matrix.PosSemidef T) :
    Matrix.trace (R * T) ≤ Matrix.trace T := by
  have hItrans : (1 - R).transpose = (1 - R) := by simp [hRt]
  have hIid : (1 - R) * (1 - R) = 1 - R := by
    noncomm_ring [hRR]
  have hgram : Matrix.PosSemidef ((1 - R) * T * (1 - R)) := by
    have hg := hT.conjTranspose_mul_mul_same (1 - R)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hItrans] at hg
    exact hg
  have hnonneg : 0 ≤ Matrix.trace ((1 - R) * T * (1 - R)) :=
    hgram.trace_nonneg
  have htrace : Matrix.trace ((1 - R) * T * (1 - R)) =
      Matrix.trace T - Matrix.trace (R * T) := by
    calc
      Matrix.trace ((1 - R) * T * (1 - R)) =
          Matrix.trace ((1 - R) * (1 - R) * T) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace ((1 - R) * T) := by rw [hIid]
      _ = Matrix.trace T - Matrix.trace (R * T) := by
        rw [sub_mul, one_mul, Matrix.trace_sub]
  linarith

private noncomputable def positiveIndicator {n : ℕ} (d : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if 0 < d i then 1 else 0

private noncomputable def indicatorProjector {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Q * Matrix.diagonal (positiveIndicator d) * Q.transpose

private theorem indicatorProjector_transpose {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    (indicatorProjector Q d).transpose = indicatorProjector Q d := by
  simp [indicatorProjector, Matrix.transpose_mul, Matrix.mul_assoc]

private theorem indicatorProjector_idempotent {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hQTQ : Q.transpose * Q = 1) :
    indicatorProjector Q d * indicatorProjector Q d = indicatorProjector Q d := by
  let D := Matrix.diagonal (positiveIndicator d)
  have hDD : D * D = D := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : 0 < d i <;> simp [positiveIndicator, hi]
  dsimp [indicatorProjector]
  calc
    (Q * D * Q.transpose) * (Q * D * Q.transpose) =
        Q * D * (Q.transpose * Q) * D * Q.transpose := by
      simp only [Matrix.mul_assoc]
    _ = Q * D * Q.transpose := by
      rw [hQTQ]
      simp [hDD, Matrix.mul_assoc]

private theorem indicatorProjector_trace {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hQTQ : Q.transpose * Q = 1) :
    Matrix.trace (indicatorProjector Q d) =
      ∑ i : Fin n, positiveIndicator d i := by
  dsimp [indicatorProjector]
  calc
    Matrix.trace (Q * Matrix.diagonal (positiveIndicator d) * Q.transpose) =
        Matrix.trace (Q.transpose * Q * Matrix.diagonal (positiveIndicator d)) := by
      rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (Matrix.diagonal (positiveIndicator d)) := by
      rw [hQTQ, one_mul]
    _ = ∑ i : Fin n, positiveIndicator d i := Matrix.trace_diagonal _

private theorem hermitianPositivePart_trace_eq_projector_mul {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    Matrix.trace (hermitianPositivePart M) =
      Matrix.trace (indicatorProjector
        (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
        hM.eigenvalues * M) := by
  let U : Matrix (Fin n) (Fin n) ℝ := hM.eigenvectorUnitary
  let d : Fin n → ℝ := hM.eigenvalues
  let D := Matrix.diagonal d
  let E := Matrix.diagonal (positiveIndicator d)
  have hUtU : U.transpose * U = 1 := by
    have hu := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hu
  have hMdiag : M = U * D * U.transpose := by
    simpa [U, D, d, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hM.spectral_theorem
  have hpart : hermitianPositivePart M =
      U * Matrix.diagonal (fun i : Fin n => max (d i) 0) * U.transpose := by
    simp only [hermitianPositivePart, dif_pos hM]
    rfl
  have hprod : indicatorProjector U d * M = U * (E * D) * U.transpose := by
    rw [hMdiag]
    dsimp [indicatorProjector]
    calc
      (U * E * U.transpose) * (U * D * U.transpose) =
          U * E * (U.transpose * U) * D * U.transpose := by
        simp only [Matrix.mul_assoc]
      _ = U * (E * D) * U.transpose := by
        rw [hUtU]
        simp [Matrix.mul_assoc]
  have htrace_conj (F : Matrix (Fin n) (Fin n) ℝ) :
      Matrix.trace (U * F * U.transpose) = Matrix.trace F := by
    calc
      Matrix.trace (U * F * U.transpose) =
          Matrix.trace (U.transpose * U * F) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace F := by rw [hUtU, one_mul]
  rw [hpart, hprod, htrace_conj, htrace_conj]
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 < d i
  · simp [positiveIndicator, hi, max_eq_left hi.le]
  · have hle : d i ≤ 0 := le_of_not_gt hi
    simp [positiveIndicator, hi, max_eq_right hle]

private theorem trace_mul_orthogonal_spectral {n : ℕ}
    (R Q : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    Matrix.trace (R * (Q * Matrix.diagonal d * Q.transpose)) =
      ∑ i : Fin n, d i * (Q.transpose * R * Q) i i := by
  calc
    Matrix.trace (R * (Q * Matrix.diagonal d * Q.transpose)) =
        Matrix.trace ((R * Q) * Matrix.diagonal d * Q.transpose) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Q.transpose * (R * Q) * Matrix.diagonal d) := by
      rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace ((Q.transpose * R * Q) * Matrix.diagonal d) := by
      simp only [Matrix.mul_assoc]
    _ = ∑ i : Fin n, d i * (Q.transpose * R * Q) i i := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem spectralMatrix_factor_variational {n : ℕ}
    (d : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.SpectralMatrix d Q =
      Q * Matrix.diagonal d * Q.transpose := by
  ext i j
  simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem indicatorProjector_selected_supported {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC) :
    selectedProjection k QAhat * indicatorProjector QC eigenvaluesC =
      indicatorProjector QC eigenvaluesC := by
  let P := selectedProjection k QAhat
  let D := Matrix.diagonal (positiveIndicator eigenvaluesC)
  have hPD : (P * QC) * D = QC * D := by
    ext i a
    dsimp only [D]
    rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
    by_cases ha : 0 < eigenvaluesC a
    · have hv := selectedCompression_positiveEigenvector_supported hAhat hC a ha
      change P *ᵥ QC.col a = QC.col a at hv
      have hcoord := congrFun hv i
      have hentry : (P * QC) i a = QC i a := by
        simpa only [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum,
          Matrix.col_apply] using hcoord
      simp [positiveIndicator, ha, hentry]
    · simp [positiveIndicator, ha]
  dsimp [indicatorProjector]
  calc
    P * (QC * D * QC.transpose) = ((P * QC) * D) * QC.transpose := by
      simp only [Matrix.mul_assoc]
    _ = (QC * D) * QC.transpose := by rw [hPD]
    _ = QC * D * QC.transpose := rfl

private theorem selectedProjection_trace_eq_rank {n k : ℕ}
    (hk : k ≤ n)
    {Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat : Fin n → ℝ}
    {QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      Ahat eigenvaluesAhat QAhat) :
    Matrix.trace (selectedProjection k QAhat) = (k : ℝ) := by
  let D : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal fun i => if i.val < k then 1 else 0
  have hQTQ : QAhat.transpose * QAhat = 1 := by
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      hAhat.2.2.1 a b
  have hP : selectedProjection k QAhat = QAhat * D * QAhat.transpose := by
    ext i j
    simp only [selectedProjection, Matrix.of_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, D]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a.val < k <;> simp [ha]
  rw [hP, Matrix.trace_mul_cycle, hQTQ, one_mul]
  simp only [D, Matrix.trace_diagonal]
  simp [Fin.card_filter_val_lt, Nat.min_eq_right hk]

private theorem positiveIndicator_trace_count {n : ℕ} (d : Fin n → ℝ) :
    (∑ i : Fin n, positiveIndicator d i) =
      ((Finset.univ.filter fun i : Fin n => 0 < d i).card : ℝ) := by
  simp only [positiveIndicator]
  simp

private theorem orthogonalProjection_difference {n : ℕ}
    (P E : Matrix (Fin n) (Fin n) ℝ)
    (hPt : P.transpose = P) (hEt : E.transpose = E)
    (hPP : P * P = P) (hEE : E * E = E)
    (hPE : P * E = E) (hEP : E * P = E) :
    (P - E).transpose = P - E ∧ (P - E) * (P - E) = P - E := by
  constructor
  · simp [hPt, hEt]
  · noncomm_ring [hPP, hEE, hPE, hEP]

private theorem orthogonalProjection_conjugate_diag_bounds {n : ℕ}
    (R Q : Matrix (Fin n) (Fin n) ℝ)
    (hRt : R.transpose = R) (hRR : R * R = R)
    (hQTQ : Q.transpose * Q = 1) (i : Fin n) :
    0 ≤ (Q.transpose * R * Q) i i ∧
      (Q.transpose * R * Q) i i ≤ 1 := by
  have hRpsd := orthogonalProjection_posSemidef R hRt hRR
  have hItrans : (1 - R).transpose = (1 - R) := by simp [hRt]
  have hIid : (1 - R) * (1 - R) = 1 - R := by
    noncomm_ring [hRR]
  have hIpsd := orthogonalProjection_posSemidef (1 - R) hItrans hIid
  have hQconj : Matrix.PosSemidef (Q.transpose * R * Q) := by
    have hg := hRpsd.conjTranspose_mul_mul_same Q
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hg
  have hIQconj : Matrix.PosSemidef (Q.transpose * (1 - R) * Q) := by
    have hg := hIpsd.conjTranspose_mul_mul_same Q
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hg
  have hdiff : Q.transpose * (1 - R) * Q = 1 - Q.transpose * R * Q := by
    calc
      Q.transpose * (1 - R) * Q = Q.transpose * Q - Q.transpose * R * Q := by
        noncomm_ring
      _ = 1 - Q.transpose * R * Q := by rw [hQTQ]
  constructor
  · exact hQconj.diag_nonneg
  · have hi := hIQconj.diag_nonneg (i := i)
    rw [hdiff] at hi
    have h : 0 ≤ 1 - (Q.transpose * R * Q) i i := by
      simpa [Matrix.sub_apply, Matrix.one_apply] using hi
    linarith

private theorem scalar_defect_weighted_le {n k : ℕ}
    (d t : Fin n → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hd : ∀ i, 0 ≤ d i)
    (htail : ∀ i : Fin n, k ≤ i.val → d i = 0)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    (∑ i : Fin n,
      (c * ((if i.val < k then (1 : ℝ) else 0) - positiveIndicator d i) +
        (c * positiveIndicator d i - d i) * t i)) ≤
      ∑ i : Fin n, if i.val < k then max (c - d i) 0 else 0 := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val < k
  · by_cases hpos : 0 < d i
    · have hδ : positiveIndicator d i = 1 := by simp [positiveIndicator, hpos]
      rw [hδ]
      simp only [hi, ↓reduceIte]
      by_cases hcd : 0 ≤ c - d i
      · rw [max_eq_left hcd]
        have hti := (ht i).2
        nlinarith
      · have hcd' : c - d i ≤ 0 := le_of_not_ge hcd
        rw [max_eq_right hcd']
        have hti := (ht i).1
        nlinarith
    · have hzero : d i = 0 := le_antisymm (le_of_not_gt hpos) (hd i)
      have hδ : positiveIndicator d i = 0 := by simp [positiveIndicator, hpos]
      rw [hzero, hδ]
      simp [hi, max_eq_left hc]
  · have hzero : d i = 0 := htail i (Nat.le_of_not_gt hi)
    have hδ : positiveIndicator d i = 0 := by simp [positiveIndicator, hzero]
    rw [hzero, hδ]
    simp [hi]

theorem matchedLeading_defect_positivePart_le_sum {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC) :
    let c := eigenvaluesA ⟨k - 1, by omega⟩
    let P := selectedProjection k QAhat
    let C := P * A * P
    Matrix.trace (hermitianPositivePart (c • P - C)) ≤
      ∑ i : Fin n, if i.val < k then max (c - eigenvaluesC i) 0 else 0 := by
  classical
  let c := eigenvaluesA ⟨k - 1, by omega⟩
  let P := selectedProjection k QAhat
  let C := P * A * P
  let M := c • P - C
  change Matrix.trace (hermitianPositivePart M) ≤
    ∑ i : Fin n, if i.val < k then max (c - eigenvaluesC i) 0 else 0
  have hc : 0 ≤ c := hA.1 ⟨k - 1, by omega⟩
  have hPt : P.transpose = P := selectedProjection_transpose k QAhat
  have hPP : P * P = P := selectedProjection_idempotent hAhat
  have hPherm : P.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    exact hPt
  have hCpsd : Matrix.PosSemidef C :=
    selectedCompression_mathlibPosSemidef hA hAhat
  have hM : M.IsHermitian := (hPherm.smul (by rfl)).sub hCpsd.1
  let U : Matrix (Fin n) (Fin n) ℝ := hM.eigenvectorUnitary
  let R := indicatorProjector U hM.eigenvalues
  have hUtU : U.transpose * U = 1 := by
    have hu := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hu
  have hRt : R.transpose = R := indicatorProjector_transpose U hM.eigenvalues
  have hRR : R * R = R := indicatorProjector_idempotent U hM.eigenvalues hUtU
  have hQCtQC : QC.transpose * QC = 1 := by
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      hC.2.2.1 a b
  let E := indicatorProjector QC eigenvaluesC
  have hEt : E.transpose = E := indicatorProjector_transpose QC eigenvaluesC
  have hEE : E * E = E := indicatorProjector_idempotent QC eigenvaluesC hQCtQC
  have hPE : P * E = E := indicatorProjector_selected_supported hAhat hC
  have hEP : E * P = E := by
    have h := congrArg Matrix.transpose hPE
    simpa [Matrix.transpose_mul, hPt, hEt] using h
  let P₀ := P - E
  have hP₀ : P₀.transpose = P₀ ∧ P₀ * P₀ = P₀ :=
    orthogonalProjection_difference P E hPt hEt hPP hEE hPE hEP
  have hP₀psd : Matrix.PosSemidef P₀ :=
    orthogonalProjection_posSemidef P₀ hP₀.1 hP₀.2
  have htraceP₀bound : Matrix.trace (R * P₀) ≤ Matrix.trace P₀ :=
    trace_mul_orthogonalProjection_le R P₀ hRt hRR hP₀psd
  let t : Fin n → ℝ := fun i => (QC.transpose * R * QC) i i
  have ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1 := by
    intro i
    exact orthogonalProjection_conjugate_diag_bounds R QC hRt hRR hQCtQC i
  have hCfactor : C = QC * Matrix.diagonal eigenvaluesC * QC.transpose := by
    calc
      C = NLA.Statements.RA10.SpectralMatrix eigenvaluesC QC := hC.2.2.2
      _ = QC * Matrix.diagonal eigenvaluesC * QC.transpose :=
        spectralMatrix_factor_variational eigenvaluesC QC
  have htraceRC : Matrix.trace (R * C) =
      ∑ i : Fin n, eigenvaluesC i * t i := by
    rw [hCfactor]
    exact trace_mul_orthogonal_spectral R QC eigenvaluesC
  have htraceRE : Matrix.trace (R * E) =
      ∑ i : Fin n, positiveIndicator eigenvaluesC i * t i := by
    exact trace_mul_orthogonal_spectral R QC (positiveIndicator eigenvaluesC)
  have htraceP : Matrix.trace P =
      ∑ i : Fin n, if i.val < k then (1 : ℝ) else 0 := by
    have h := selectedProjection_trace_eq_rank (Nat.le_of_lt hkn) hAhat
    rw [h]
    simp [Fin.card_filter_val_lt,
      Nat.min_eq_right (Nat.le_of_lt hkn)]
  have htraceE : Matrix.trace E =
      ∑ i : Fin n, positiveIndicator eigenvaluesC i :=
    indicatorProjector_trace QC eigenvaluesC hQCtQC
  have htraceP₀ : Matrix.trace P₀ =
      ∑ i : Fin n,
        ((if i.val < k then (1 : ℝ) else 0) - positiveIndicator eigenvaluesC i) := by
    dsimp [P₀]
    rw [Matrix.trace_sub, htraceP, htraceE, Finset.sum_sub_distrib]
  have htraceM : Matrix.trace (R * M) =
      c * Matrix.trace (R * P₀) +
        c * Matrix.trace (R * E) - Matrix.trace (R * C) := by
    have hPEsum : P = P₀ + E := by dsimp [P₀]; abel
    dsimp [M]
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul,
      Matrix.trace_smul, hPEsum, Matrix.mul_add, Matrix.trace_add]
    simp [smul_eq_mul]
    ring
  have htail : ∀ i : Fin n, k ≤ i.val → eigenvaluesC i = 0 := by
    intro i hi
    exact selectedCompression_eigenvalues_tail_zero
      (Nat.le_of_lt hkn) hAhat hC i hi
  have hnumeric := scalar_defect_weighted_le
    (k := k) eigenvaluesC t c hc hC.1 htail ht
  calc
    Matrix.trace (hermitianPositivePart M) = Matrix.trace (R * M) :=
      hermitianPositivePart_trace_eq_projector_mul M hM
    _ = c * Matrix.trace (R * P₀) +
        (∑ i : Fin n,
          (c * positiveIndicator eigenvaluesC i - eigenvaluesC i) * t i) := by
      rw [htraceM, htraceRE, htraceRC]
      have hsum :
          c * (∑ i : Fin n, positiveIndicator eigenvaluesC i * t i) -
              (∑ i : Fin n, eigenvaluesC i * t i) =
            ∑ i : Fin n,
              (c * positiveIndicator eigenvaluesC i - eigenvaluesC i) * t i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      calc
        c * Matrix.trace (R * P₀) +
            c * (∑ i : Fin n, positiveIndicator eigenvaluesC i * t i) -
            (∑ i : Fin n, eigenvaluesC i * t i) =
            c * Matrix.trace (R * P₀) +
              (c * (∑ i : Fin n, positiveIndicator eigenvaluesC i * t i) -
                (∑ i : Fin n, eigenvaluesC i * t i)) := by ring
        _ = _ := by rw [hsum]
    _ ≤ c * Matrix.trace P₀ +
        (∑ i : Fin n,
          (c * positiveIndicator eigenvaluesC i - eigenvaluesC i) * t i) := by
      exact add_le_add (mul_le_mul_of_nonneg_left htraceP₀bound hc) le_rfl
    _ = ∑ i : Fin n,
        (c * ((if i.val < k then (1 : ℝ) else 0) - positiveIndicator eigenvaluesC i) +
          (c * positiveIndicator eigenvaluesC i - eigenvaluesC i) * t i) := by
      rw [htraceP₀, Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ ∑ i : Fin n,
        if i.val < k then max (c - eigenvaluesC i) 0 else 0 := hnumeric

theorem matchedLeading_defect_le_loss {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let c := eigenvaluesA ⟨k - 1, by omega⟩
    let P := selectedProjection k QAhat
    let C := P * A * P
    let L := (∑ i : Fin n, if i.val < k then eigenvaluesA i else 0) - Matrix.trace C
    Matrix.trace (hermitianPositivePart (c • P - C)) ≤ L := by
  obtain ⟨eigenvaluesC, QC, hC⟩ := selectedCompression_exists_orderedPSD hA hAhat
  exact (matchedLeading_defect_positivePart_le_sum hk hkn hA hAhat hC).trans
    (matchedLeading_defect_sum_le_loss hk hkn hA hAhat hC)

#assert_trust kernel matchedLeading_defect_positivePart_le_sum
#assert_trust kernel matchedLeading_defect_le_loss
#print axioms matchedLeading_defect_le_loss

#assert_trust kernel indicatorProjector_idempotent
#assert_trust kernel hermitianPositivePart_trace_eq_projector_mul

#assert_trust kernel orthogonalProjection_posSemidef
#assert_trust kernel trace_mul_orthogonalProjection_le

end NLA.Proofs.RA10
