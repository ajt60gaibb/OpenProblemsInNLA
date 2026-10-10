import NLA.Proofs.RA10.SelectedCompressionPSD
import NLA.Proofs.RA10.SelectedCompressionPrefixSupport
import NLA.Proofs.RA10.OrderedSpectralIntersection
import Mathlib.Tactic.Ring

/-! RA-10 exact coefficient-one comparison between eigenvalues of the actual
selected compression C = P A P and A. Nuclear pinching and the full transfer
target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

theorem selectedCompression_supported_quadratic_eq {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat : Fin n → ℝ}
    {QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (x : Fin n → ℝ)
    (hx : selectedProjection k QAhat *ᵥ x = x) :
    (∑ i : Fin n, ∑ j : Fin n,
      x i * (selectedProjection k QAhat * A * selectedProjection k QAhat) i j * x j) =
      ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := by
  have hquad := selectedCompression_quadratic_form (k := k) (A := A) hAhat x
  dsimp at hquad
  simpa only [hx] using hquad

theorem nonzero_vector_sum_sq_pos {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    0 < ∑ i : Fin n, x i ^ 2 := by
  have hex : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j))
    ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

theorem selectedCompression_eigenvalues_nonneg_le {n k : ℕ}
    (hk : k ≤ n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    (a : Fin n) (ha : a.val < k) :
    0 ≤ eigenvaluesC a ∧ eigenvaluesC a ≤ eigenvaluesA a := by
  have _ : k ≤ n := hk
  have _ : a.val < k := ha
  constructor
  · exact hC.1 a
  · by_cases hzero : eigenvaluesC a = 0
    · simpa only [hzero] using hA.1 a
    · have hpos : 0 < eigenvaluesC a :=
        lt_of_le_of_ne (hC.1 a) (Ne.symm hzero)
      obtain ⟨x, hxne, hxC, hxA⟩ :=
        orderedSpectral_prefix_suffix_nonzero_intersection QC QA a
      have hPx := selectedCompression_positivePrefix_supported hAhat hC a hpos x hxC
      have hqeq := selectedCompression_supported_quadratic_eq (k := k) (A := A)
        hAhat x hPx
      have hCbound := orderedPSDSpectral_rayleigh_lower_prefix hC a x hxC
      have hAbound := orderedPSDSpectral_rayleigh_upper_suffix hA a x hxA
      have hspos := nonzero_vector_sum_sq_pos x hxne
      have hmul : eigenvaluesC a * (∑ i : Fin n, x i ^ 2) ≤
          eigenvaluesA a * (∑ i : Fin n, x i ^ 2) := by
        calc
          eigenvaluesC a * (∑ i : Fin n, x i ^ 2) ≤
              ∑ i : Fin n, ∑ j : Fin n,
                x i * (selectedProjection k QAhat * A * selectedProjection k QAhat) i j * x j :=
            hCbound
          _ = ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := hqeq
          _ ≤ eigenvaluesA a * (∑ i : Fin n, x i ^ 2) := hAbound
      exact (mul_le_mul_iff_of_pos_right hspos).mp hmul

#assert_trust kernel selectedCompression_supported_quadratic_eq
#assert_trust kernel nonzero_vector_sum_sq_pos
#assert_trust kernel selectedCompression_eigenvalues_nonneg_le
#print axioms selectedCompression_eigenvalues_nonneg_le

end NLA.Proofs.RA10
