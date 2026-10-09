import OAI.Analysis.DirectCrouzeix.DomainBound

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix

open Set Metric

theorem convex_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Convex ℝ (numericalRange A) :=
  Geometry.convex_quadratic_range (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).toLinearMap

theorem complete_crouzeix : UniversalBound 2 := by
  intro n m d hn hm A B
  let M := rangeMaximum A B
  have hM : 0 ≤ M := by
    obtain ⟨z,hz,he⟩ := rangeMaximum_attained hn A B
    rw [show M = ‖polynomialValue B z‖ from he.symm]
    exact norm_nonneg _
  apply le_of_forall_pos_le_add
  intro ε hε
  let ρ := M+ε/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hMρ : M < ρ := by dsimp [ρ]; linarith
  let V := {z : ℂ | ‖polynomialValue B z‖ < ρ}
  have hV : IsOpen V := isOpen_lt (continuous_polynomialValue B).norm continuous_const
  have hWV : numericalRange A ⊆ V := by
    intro z hz
    exact lt_of_le_of_lt (norm_polynomialValue_le_rangeMaximum A B hz) hMρ
  obtain ⟨δ,hδ,hδV⟩ := (isCompact_numericalRange A).exists_thickening_subset_open hV hWV
  obtain ⟨D,v,b,hW,hc,hnear⟩ := Geometry.exists_exponential_outer (isCompact_numericalRange A)
    (numericalRange_nonempty hn A) (convex_numericalRange A) hδ
  have hbound : ∀ z, Geometry.expLevel v b z ≤ 1 →
      ‖matrixPolynomialValue z (coefficientPolynomial B)‖ ≤ ρ := by
    intro z hz
    rw [matrixPolynomialValue_coefficientPolynomial]
    apply le_of_lt
    apply hδV
    obtain ⟨w,hw,hzw⟩ := hnear z hz
    exact mem_thickening_iff.mpr ⟨w,hw,by simpa only [dist_eq_norm] using hzw⟩
  have hh := expLevel_domain_bound_scaled hn hm A v b hc hW (coefficientPolynomial B) hρ hbound
  rw [tensorPolynomial_coefficientPolynomial] at hh
  calc
    ‖tensorEvaluation A B‖ ≤ 2*ρ := hh
    _ = 2*rangeMaximum A B+ε := by dsimp [ρ,M]; ring

end DirectCrouzeix

end

end

end

end

end

end

end

end

end

end OAI
