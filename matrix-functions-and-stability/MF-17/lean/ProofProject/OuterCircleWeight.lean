import ProofProject.PositiveCircleFactorization
import ProofProject.CircleGramPolynomial

/-!
# An outer polynomial for the finite Hilbert-family weight

This realizes the positive circle weight by an actual scalar polynomial.
The closed-disk nonvanishing, degree, and boundary modulus are all proved.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

universe u

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

theorem exists_outerPolynomial_reverseCircleWeight (v : Fin n → H) (hn : 1 ≤ n)
    (hpos : ∀ z : AddCircle (1 : ℝ), 0 < reverseCircleWeight v z) :
    ∃ h : Polynomial ℂ, h.natDegree ≤ n - 1 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0) ∧
      ∀ z : AddCircle (1 : ℝ),
        ‖h.eval (fourier 1 z)‖ ^ 2 = reverseCircleWeight v z := by
  obtain ⟨h, hdeg, hnz, hfactor⟩ := positiveCirclePhase_factorization (n - 1)
    (circleGramPolynomial v) (circleGramPolynomial_natDegree_le v hn)
    (circleGramPolynomial_positive_phase v hn hpos)
  refine ⟨h, hdeg, hnz, ?_⟩
  intro z
  have hnorm := finiteCircle_fourier_norm 1 z
  have hchar : fourier 1 z ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)
  have heq := (hfactor (fourier 1 z) hnorm).symm.trans (circleGramPolynomial_eval_fourier v hn z)
  have heq' := mul_left_cancel₀ (pow_ne_zero (n - 1) hchar) heq
  exact Complex.ofReal_injective heq'

/-- The actual coefficient-tail hypothesis supplies the positive weight needed
by finite factorization, with no additional geometry or existence premise. -/
theorem exists_outerPolynomial_of_tail_bound {v : Fin n → H} {K : ℝ}
    (h : HasSynthesisTailBound v K) (hn : 1 ≤ n) (hv : ∃ j, v j ≠ 0) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ n - 1 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0) ∧
      ∀ z : AddCircle (1 : ℝ),
        ‖p.eval (fourier 1 z)‖ ^ 2 = reverseCircleWeight v z :=
  exists_outerPolynomial_reverseCircleWeight v hn (reverseCircleWeight_pos h hv)

lemma outerPolynomial_circle_mean (v : Fin n → H) (p : Polynomial ℂ)
    (hp : ∀ z : AddCircle (1 : ℝ),
      ‖p.eval (fourier 1 z)‖ ^ 2 = reverseCircleWeight v z) :
    (∫ z : AddCircle (1 : ℝ), ‖p.eval (fourier 1 z)‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑ j, ‖v j‖ ^ 2 := by
  simp_rw [hp]
  exact reverseCircleWeight_integral v

lemma outerPolynomial_value_one (v : Fin n → H) (p : Polynomial ℂ)
    (hp : ∀ z : AddCircle (1 : ℝ),
      ‖p.eval (fourier 1 z)‖ ^ 2 = reverseCircleWeight v z) :
    ‖p.eval 1‖ ^ 2 = ‖finiteSynthesis v (fun _ => 1)‖ ^ 2 := by
  simpa only [fourier_eval_zero, reverseCircleWeight_at_zero] using hp 0

/-- The finite weighted projection estimate transfers to the polynomial
factor without changing its constant. -/
theorem outerPolynomial_nonnegative_projection_le {v : Fin n → H} {K : ℝ}
    (h : HasSynthesisTailBound v K) (p : Polynomial ℂ)
    (hp : ∀ z : AddCircle (1 : ℝ),
      ‖p.eval (fourier 1 z)‖ ^ 2 = reverseCircleWeight v z) (c : ℤ →₀ ℂ) :
    (∫ z : AddCircle (1 : ℝ),
      ‖laurentCirclePolynomial (c.filter (fun m => 0 ≤ m)) z‖ ^ 2 *
        ‖p.eval (fourier 1 z)‖ ^ 2 ∂AddCircle.haarAddCircle) ≤
      K ^ 2 * ∫ z : AddCircle (1 : ℝ),
        ‖laurentCirclePolynomial c z‖ ^ 2 * ‖p.eval (fourier 1 z)‖ ^ 2
          ∂AddCircle.haarAddCircle := by
  simp_rw [hp]
  exact weightedCircle_nonnegative_projection_le h c

end ProofProject
