import OAI.Analysis.DirectCrouzeix.BoundaryEnergy

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

abbrev MatrixPolynomial (m : ℕ) := Polynomial (Matrix (Fin m) (Fin m) ℂ)

def matrixPolynomialValue {m : ℕ} (z : ℂ) :
    MatrixPolynomial m →+* Matrix (Fin m) (Fin m) ℂ :=
  Polynomial.eval₂RingHom' (RingHom.id _) (z • 1) (by
    intro C
    change C * (z • 1) = (z • 1) * C
    simp [])

@[simp] theorem matrixPolynomialValue_C {m : ℕ} (z : ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) : matrixPolynomialValue z (Polynomial.C C) = C := by
  exact Polynomial.eval₂_C _ _

@[simp] theorem matrixPolynomialValue_X {m : ℕ} (z : ℂ) :
    matrixPolynomialValue (m := m) z Polynomial.X = z • 1 := by
  exact Polynomial.eval₂_X _ _

theorem continuous_matrixPolynomialValue {m : ℕ} (G : MatrixPolynomial m) :
    Continuous (fun z => matrixPolynomialValue z G) :=
  (G.continuous_eval₂ (RingHom.id _)).comp (continuous_id.smul continuous_const)

def scalarMatrixPolynomial {m : ℕ} (p : Polynomial ℂ) : MatrixPolynomial m :=
  p.map (algebraMap ℂ (Matrix (Fin m) (Fin m) ℂ))

theorem matrixPolynomialValue_scalar {m : ℕ} (p : Polynomial ℂ) (z : ℂ) :
    matrixPolynomialValue (m := m) z (scalarMatrixPolynomial p) = p.eval z • 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [scalarMatrixPolynomial,Polynomial.map_add,map_add] at *
    rw [hp,hq,Polynomial.eval_add,add_smul]
  | monomial k c =>
    simp only [scalarMatrixPolynomial,← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,map_mul,map_pow,matrixPolynomialValue_C,matrixPolynomialValue_X,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    simp only [Algebra.algebraMap_eq_smul_one,smul_pow,one_pow,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,smul_smul]
    rw [mul_comm]

theorem tensorPolynomial_scalar {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (p : Polynomial ℂ) :
    tensorPolynomial (m := m) A (scalarMatrixPolynomial p) = (Polynomial.aeval A p) ⊗ₖ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [scalarMatrixPolynomial,Polynomial.map_add,map_add] at *
    rw [hp,hq,Matrix.add_kronecker]
  | monomial k c =>
    simp only [scalarMatrixPolynomial,← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,map_mul,map_pow,tensorPolynomial_C,tensorPolynomial_X,Polynomial.aeval_C,
      Polynomial.aeval_X,kronecker_pow_one,Algebra.algebraMap_eq_smul_one,
      Matrix.smul_kronecker,Matrix.kronecker_smul,← Matrix.mul_kronecker_mul,
      Matrix.smul_mul,Matrix.one_mul,Matrix.mul_one]

def faberPolynomial {m N : ℕ} (b : ℕ → Polynomial ℂ)
    (C : Fin N → Matrix (Fin m) (Fin m) ℂ) : MatrixPolynomial m :=
  ∑ k : Fin N, Polynomial.C (C k) * scalarMatrixPolynomial (b k)

theorem matrixPolynomialValue_faber {m N : ℕ} (b : ℕ → Polynomial ℂ)
    (C : Fin N → Matrix (Fin m) (Fin m) ℂ) (z : ℂ) :
    matrixPolynomialValue z (faberPolynomial b C) = ∑ k : Fin N, (b k).eval z • C k := by
  simp only [faberPolynomial,map_sum,map_mul,matrixPolynomialValue_C,matrixPolynomialValue_scalar,
    Matrix.mul_smul,Matrix.mul_one]

theorem tensorPolynomial_faber {n m N : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ) :
    tensorPolynomial A (faberPolynomial b C) = ∑ k : Fin N, Polynomial.aeval A (b k) ⊗ₖ C k := by
  simp only [faberPolynomial,map_sum,map_mul,tensorPolynomial_C,tensorPolynomial_scalar,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]

theorem faber_pairing {n m N : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (X Y : Matrix (Fin n) (Fin m) ℂ) :
    inner ℂ (hsVector Y) (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ)
      (tensorPolynomial A (faberPolynomial b C)) (hsVector X)) =
      ∑ k : Fin N, entryPair (Yᴴ * Polynomial.aeval A (b k) * X) (C k) := by
  simp only [tensorPolynomial_faber,map_sum,sum_apply,inner_sum,tensor_entryPair]

def polynomialEnergy {m : ℕ} (h : BoundaryCircle → ℂ) (G : MatrixPolynomial m) : ℝ :=
  ∫ t, hsSq (matrixPolynomialValue (h t) G) ∂circleMeasure

theorem polynomialEnergy_nonneg {m : ℕ} (h : BoundaryCircle → ℂ) (G : MatrixPolynomial m) :
    0 ≤ polynomialEnergy h G := integral_nonneg (fun _ => hsSq_nonneg _)

theorem polynomialEnergy_mul_le {m : ℕ} (h : BoundaryCircle → ℂ) (hh : Continuous h)
    (F G : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (h t) F‖ ≤ 1) :
    polynomialEnergy h (F * G) ≤ polynomialEnergy h G ∧
    polynomialEnergy h (G * F) ≤ polynomialEnergy h G := by
  have hint (H : MatrixPolynomial m) :
      Integrable (fun t => hsSq (matrixPolynomialValue (h t) H)) circleMeasure :=
    continuous_integrable_compact _
      (continuous_hsSq.comp ((continuous_matrixPolynomialValue H).comp hh))
  constructor
  · apply integral_mono (hint _) (hint _)
    intro t
    change hsSq (matrixPolynomialValue (h t) (F * G)) ≤ _
    rw [map_mul]
    exact (hsSq_mul_le _ _).trans (by
      have hn := pow_le_pow_left₀ (norm_nonneg _) (hF t) 2
      simpa using mul_le_mul_of_nonneg_right hn (hsSq_nonneg (matrixPolynomialValue (h t) G)))
  · apply integral_mono (hint _) (hint _)
    intro t
    change hsSq (matrixPolynomialValue (h t) (G * F)) ≤ _
    rw [map_mul]
    exact (hsSq_mul_le_right _ _).trans (by
      have hn := pow_le_pow_left₀ (norm_nonneg _) (hF t) 2
      simpa using mul_le_mul_of_nonneg_left hn (hsSq_nonneg (matrixPolynomialValue (h t) G)))

theorem cross_boundary_estimate {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (h : BoundaryCircle → ℂ)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (X Y : Matrix (Fin n) (Fin m) ℂ) (G : MatrixPolynomial m) :
    ‖inner ℂ (hsVector Y) (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ)
      (tensorPolynomial A G) (hsVector X))‖ ^ 2 ≤
      (∫ t, hsSq (Yᴴ * R t * X) ∂circleMeasure) * polynomialEnergy h G := by
  obtain ⟨N,C,rfl⟩ := hexpand G
  rw [faber_pairing]
  let M := fun t => Yᴴ * R t * X
  have hM : Continuous M := (compressionCLM X Y).continuous.comp hR
  have hMc (k : ℕ) : fourierCoeff M (-(k : ℤ)) = Yᴴ * Polynomial.aeval A (b k) * X := by
    rw [fourierCoeff_compression X Y R hR,hcoeff]
  have hb := finite_negative_bessel M hM N
  simp_rw [hMc] at hb
  have hb0 : 0 ≤ ∫ t, hsSq (M t) ∂circleMeasure := integral_nonneg (fun _ => hsSq_nonneg _)
  exact (norm_sum_entryPair_sq_le _ C).trans
    ((mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg (fun _ _ => hsSq_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (hlower N C) hb0))

theorem singular_ordered_pairings {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (F G : MatrixPolynomial m) (x y : EuclideanSpace ℂ (Fin n × Fin m)) (γ : ℝ)
    (hFx : Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F) x =
      (γ : ℂ) • y)
    (hFy : ContinuousLinearMap.adjoint
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F)) y =
      (γ : ℂ) • x) :
    inner ℂ y (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A (F * G)) x) =
      (γ : ℂ)
      * inner ℂ x (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A G) x) ∧
    inner ℂ y (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A (G * F)) x) =
      (γ : ℂ)
      * inner ℂ y (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A G) y) := by
  simp only [map_mul,mul_apply_eq_comp]
  constructor
  · rw [← ContinuousLinearMap.adjoint_inner_left,hFy,inner_smul_left]
    simp
  · rw [hFx,map_smul,inner_smul_right]

theorem singular_diagonal_estimates {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℕ → Polynomial ℂ) (h : BoundaryCircle → ℂ) (hh : Continuous h)
    (hexpand : ∀ G : MatrixPolynomial m, ∃ (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      G = faberPolynomial b C)
    (hlower : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      ∑ k, hsSq (C k) ≤ polynomialEnergy h (faberPolynomial b C))
    (hupper : ∀ N (C : Fin N → Matrix (Fin m) (Fin m) ℂ),
      polynomialEnergy h (faberPolynomial b C) ≤ ∑ k : Fin N, faberWeight k * hsSq (C k))
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R)
    (hcoeff : ∀ k : ℕ, fourierCoeff R (-(k : ℤ)) = Polynomial.aeval A (b k))
    (F : MatrixPolynomial m) (hF : ∀ t, ‖matrixPolynomialValue (h t) F‖ ≤ 1)
    (X Y : Matrix (Fin n) (Fin m) ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hFx : Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F) (hsVector X) =
      (γ : ℂ) • hsVector Y)
    (hFy : ContinuousLinearMap.adjoint
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (tensorPolynomial A F)) (hsVector Y) =
      (γ : ℂ) • hsVector X) :
    let a := ∫ t, hsSq (Yᴴ * R t * X) ∂circleMeasure
    (hsSq (Xᴴ * Polynomial.aeval A (b 0) * X) + (1/2 : ℝ) *
      ∑' k : ℕ, hsSq (Xᴴ * Polynomial.aeval A (b (k+1)) * X) ≤ a / γ^2) ∧
    (hsSq (Yᴴ * Polynomial.aeval A (b 0) * Y) + (1/2 : ℝ) *
      ∑' k : ℕ, hsSq (Yᴴ * Polynomial.aeval A (b (k+1)) * Y) ≤ a / γ^2) := by
  dsimp only
  let a := ∫ t, hsSq (Yᴴ * R t * X) ∂circleMeasure
  have ha : 0 ≤ a := integral_nonneg (fun _ => hsSq_nonneg _)
  have hdiv : 0 ≤ a / γ^2 := div_nonneg ha (sq_nonneg _)
  have htest (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ) :=
    singular_ordered_pairings A F (faberPolynomial b C) (hsVector X) (hsVector Y) γ hFx hFy
  have hbound (N : ℕ) (C : Fin N → Matrix (Fin m) (Fin m) ℂ) :
      (‖∑ k : Fin N, entryPair (Xᴴ * Polynomial.aeval A (b k) * X) (C k)‖^2 ≤
        (a / γ^2) * ∑ k : Fin N, faberWeight k * hsSq (C k)) ∧
      (‖∑ k : Fin N, entryPair (Yᴴ * Polynomial.aeval A (b k) * Y) (C k)‖^2 ≤
        (a / γ^2) * ∑ k : Fin N, faberWeight k * hsSq (C k)) := by
    have hs := htest N C
    simp only [faber_pairing] at hs
    have hv := cross_boundary_estimate A b h hexpand hlower R hR hcoeff X Y
    have hl := hv (F * faberPolynomial b C)
    have hr := hv (faberPolynomial b C * F)
    rw [hs.1,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hγ,mul_pow] at hl
    rw [hs.2,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hγ,mul_pow] at hr
    have hm := polynomialEnergy_mul_le h hh F (faberPolynomial b C) hF
    have hl' := hl.trans (mul_le_mul_of_nonneg_left (hm.1.trans (hupper N C)) ha)
    have hr' := hr.trans (mul_le_mul_of_nonneg_left (hm.2.trans (hupper N C)) ha)
    constructor
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
      convert hl' using 1 ; ring
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
      convert hr' using 1 ; ring
  constructor
  · exact weighted_sequence_dual (fun k => Xᴴ * Polynomial.aeval A (b k) * X)
      (a / γ^2) hdiv (fun N C => (hbound N C).1)
  · exact weighted_sequence_dual (fun k => Yᴴ * Polynomial.aeval A (b k) * Y)
      (a / γ^2) hdiv (fun N C => (hbound N C).2)

end DirectCrouzeix

end

end OAI
