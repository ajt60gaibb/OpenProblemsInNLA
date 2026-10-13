import NLA.Proofs.RA10.SelectedCompressionComparison

/-! RA-10: coefficient-one ordered PSD eigenvalue comparison from the
frozen real quadratic-form order. This generic min-max gate does not prove
the nuclear ideal inequalities or the final Target. -/

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

theorem orderedPSDSpectral_eigenvalues_le_of_psd_sub {n : ℕ}
    {G H : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesG eigenvaluesH : Fin n → ℝ}
    {QG QH : Matrix (Fin n) (Fin n) ℝ}
    (hG : NLA.Statements.RA10.OrderedPSDSpectralDecomposition G eigenvaluesG QG)
    (hH : NLA.Statements.RA10.OrderedPSDSpectralDecomposition H eigenvaluesH QH)
    (hGH : NLA.Statements.RA10.PositiveSemidefinite (G - H))
    (a : Fin n) :
    eigenvaluesH a ≤ eigenvaluesG a := by
  obtain ⟨x, hxne, hxH, hxG⟩ :=
    orderedSpectral_prefix_suffix_nonzero_intersection QH QG a
  have hHbound := orderedPSDSpectral_rayleigh_lower_prefix hH a x hxH
  have hGbound := orderedPSDSpectral_rayleigh_upper_suffix hG a x hxG
  have hqeq :
      (∑ i : Fin n, ∑ j : Fin n, x i * (G - H) i j * x j) =
        (∑ i : Fin n, ∑ j : Fin n, x i * G i j * x j) -
          (∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j) := by
    simp_rw [Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  have hqle :
      (∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j) ≤
        (∑ i : Fin n, ∑ j : Fin n, x i * G i j * x j) := by
    have hnonneg := hGH.2 x
    rw [hqeq] at hnonneg
    linarith
  have hspos := nonzero_vector_sum_sq_pos x hxne
  have hmul : eigenvaluesH a * (∑ i : Fin n, x i ^ 2) ≤
      eigenvaluesG a * (∑ i : Fin n, x i ^ 2) := by
    calc
      eigenvaluesH a * (∑ i : Fin n, x i ^ 2) ≤
          ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j := hHbound
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, x i * G i j * x j := hqle
      _ ≤ eigenvaluesG a * (∑ i : Fin n, x i ^ 2) := hGbound
  exact (mul_le_mul_iff_of_pos_right hspos).mp hmul

#assert_trust kernel orderedPSDSpectral_eigenvalues_le_of_psd_sub
#print axioms orderedPSDSpectral_eigenvalues_le_of_psd_sub

end NLA.Proofs.RA10
