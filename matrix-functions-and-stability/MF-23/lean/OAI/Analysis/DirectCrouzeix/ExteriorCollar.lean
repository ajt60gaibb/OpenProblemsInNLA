import OAI.Analysis.DirectCrouzeix.FaberCalculus

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix

open MeasureTheory Set Filter Metric

open scoped Topology ComplexConjugate MatrixOrder ComplexOrder

theorem faber_matrix_coefficient_bounds {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, Faber.chordDenominator c g u v ≠ 0)
    (hpositive : ∀ t s, 0 ≤ Faber.boundaryKernel c g t s)
    {m N : ℕ} (C : Fin N → Matrix (Fin m) (Fin m) ℂ) :
    (∑ k, hsSq (C k) ≤ polynomialEnergy (Faber.boundary c g) (faberPolynomial (Faber.faberBasis c g) C))
    ∧
      (polynomialEnergy (Faber.boundary c g) (faberPolynomial (Faber.faberBasis c g) C) ≤
        ∑ k : Fin N, faberWeight k * hsSq (C k)) := by
  have hh := Faber.faber_hilbert_coefficient_bounds hR hg hc hH hpositive (fun k => hsVector (C k))
  have he (t : Faber.Angle) :
      Faber.faberBoundarySeries c g (fun k => hsVector (C k)) t =
        hsVector (matrixPolynomialValue (Faber.boundary c g t) (faberPolynomial (Faber.faberBasis c g) C)) := by
    rw [matrixPolynomialValue_faber]
    ext p
    simp [Faber.faberBoundarySeries,hsVector,Matrix.sum_apply,Matrix.smul_apply]
  simp_rw [he,← hsSq_eq_norm_hsVector_sq] at hh
  exact hh

theorem faber_resolvent_data {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (houtside : ∀ ζ : ℂ, 1 ≤ ‖ζ‖ → Faber.exterior c g ζ ∉ numericalRange A)
    (hsupport : ∀ t, ∀ w ∈ numericalRange A,
      0 ≤ (conj (Faber.boundaryNormal c g t) * (Faber.boundary c g t-w)).re) :
    ∃ Q : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ,
      Continuous Q ∧
      (∀ k : ℕ, fourierCoeff Q (-(k:ℤ)) = Polynomial.aeval A (Faber.faberBasis c g k)) ∧
      (∀ k : ℤ, 0 < k → fourierCoeff Q k = 0) ∧
      (∀ t, (Q t+(Q t)ᴴ).PosSemidef) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Q := fun t : Faber.Angle => Faber.algebraGenerating c g A (Faber.unitPoint t)⁻¹
  have hu : ∀ u ∈ closedBall (0:ℂ) 1, IsUnit (Faber.algebraDenominator c g A u) := by
    intro u hu
    by_cases hu0 : u = 0
    · subst u
      simpa [Faber.algebraDenominator,Algebra.smul_def] using
        (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ))
    · rw [Faber.algebraDenominator_exterior c g A hu0,Algebra.smul_def]
      apply IsUnit.mul ((isUnit_iff_ne_zero.mpr hu0).map (algebraMap ℂ _))
      apply isUnit_resolvent_of_not_mem A
      apply houtside
      rw [norm_inv,one_le_inv₀ (norm_pos_iff.mpr hu0)]
      simpa [mem_closedBall,dist_zero_right] using hu
  have hd := Faber.algebraGenerating_fourier hR hc hg A hu
  refine ⟨Q,hd.1,hd.2.1,hd.2.2,?_⟩
  intro t
  have he : Q t = Faber.boundaryNormal c g t • (Faber.boundary c g t • 1-A)⁻¹ := by
    change Faber.algebraGenerating c g A (Faber.unitPoint t)⁻¹ = _
    rw [Faber.algebraGenerating_exterior c g A (Faber.unitPoint_ne_zero t)]
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  rw [he]
  exact positive_resolvent A _ _ (houtside _ (by rw [Faber.unitPoint_norm])) (hsupport t)

theorem exterior_collar_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hinj : InjOn (Faber.exterior c g) (Inv.inv ⁻¹' ball 0 R \ {0}))
    (hder : ∀ ζ : ℂ, ζ ≠ 0 → ζ⁻¹ ∈ ball 0 R → deriv (Faber.exterior c g) ζ ≠ 0)
    (hboundary : ∀ t s, 0 ≤ (conj (Faber.boundaryNormal c g t) *
      (Faber.boundary c g t-Faber.boundary c g s)).re)
    (houtside : ∀ ζ : ℂ, 1 ≤ ‖ζ‖ → Faber.exterior c g ζ ∉ numericalRange A)
    (hsupport : ∀ t, ∀ w ∈ numericalRange A,
      0 ≤ (conj (Faber.boundaryNormal c g t) * (Faber.boundary c g t-w)).re)
    (F : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (Faber.boundary c g t) F‖ ≤ 1) :
    ‖tensorPolynomial A F‖ ≤ 2 := by
  have hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, Faber.chordDenominator c g u v ≠ 0 :=
    fun _ hu _ hv => Faber.chordDenominator_ne_zero (convex_ball 0 R) hg hc hinj hder hu hv
  have hp := Faber.boundaryKernel_nonnegative hR hg hH hboundary
  have hcs (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ) := faber_matrix_coefficient_bounds hR hg hc hH hp C
  obtain ⟨Q,hQ,hcoeff,hpos,hPSD⟩ := faber_resolvent_data hn A hR hg hc houtside hsupport
  apply analytic_domain_core hn hm A (Faber.faberBasis c g) (Faber.faberBasis_zero hc g)
    (Faber.boundary c g) (Faber.continuous_boundary hR hg c)
    (faber_expansion_of_degree hm _ (Faber.faberBasis_degree hc (hg 0 (mem_ball_self (by linarith)))))
    (fun N C => (hcs N C).1) (fun N C => (hcs N C).2) Q hQ hcoeff hpos hPSD F hF

end DirectCrouzeix

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

end Conformal

end DirectCrouzeix

end

end

end

end OAI
