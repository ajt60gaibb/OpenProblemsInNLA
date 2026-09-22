import NLA.IE21.QuadraticNet
import NLA.IE21.Chernoff
import NLA.IE21.CovarianceConcentration
import NLA.IE21.RatioAlgebra

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NLA.IE21

example {n : ℕ} (B : Space n →L[ℝ] Space n)
    (x y : Space n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |inner ℝ (B x) x - inner ℝ (B y) y| ≤ 2 * ‖B‖ * ‖x - y‖ := by
  exact quadratic_lipschitz B x y hx hy

example {n : ℕ} (B : Space n →L[ℝ] Space n)
    (hB : B.IsSymmetric) (M : ℝ) (hM : 0 ≤ M)
    (hunit : ∀ x : Space n, ‖x‖ = 1 → |inner ℝ (B x) x| ≤ M) : ‖B‖ ≤ M := by
  exact symmetric_norm_le_of_unit_quadratic B hB M hM hunit

example {n : ℕ} (B : Space n →L[ℝ] Space n)
    (hB : B.IsSymmetric) (C : Finset (Space n))
    (hC : ∀ y ∈ C, ‖y‖ = 1) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : 2 * δ < 1)
    (hcover : ∀ x : Space n, ‖x‖ = 1 → ∃ y ∈ C, ‖x - y‖ ≤ δ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ y ∈ C, |inner ℝ (B y) y| ≤ M) :
    ‖B‖ ≤ M / (1 - 2 * δ) := by
  exact symmetric_norm_le_net B hB C hC δ hδ hδ' hcover M hM hbound

example {m n : ℕ} (A : Mat m n) :
    (covarianceOperator A).IsSymmetric := by
  exact covarianceOperator_symmetric A

example {m n : ℕ} (A : Mat m n) (x : Space n) (hx : ‖x‖ = 1) :
    inner ℝ (covarianceOperator A x) x = (n : ℝ) / m * ‖matrixMap A x‖ ^ 2 - 1 := by
  exact covariance_quadratic_norm A x hx

example {m n : ℕ} (A : Mat m n) (C : Finset (Space n))
    (hC : ∀ y ∈ C, ‖y‖ = 1)
    (hcover : ∀ x : Space n, ‖x‖ = 1 → ∃ y ∈ C, ‖x - y‖ ≤ (1 : ℝ) / 4)
    (t : ℝ) (ht : 0 ≤ t) (hbad : t < covarianceError A) :
    ∃ y ∈ C, t / 2 < |inner ℝ (covarianceOperator A y) y| := by
  exact covariance_net_witness A C hC hcover t ht hbad

example {m n : ℕ} (A : Mat m n) (x : Space n) (i : Fin m) :
    matrixMap A x i = inner ℝ (matrixRow A i) x := by
  exact matrixMap_eq_inner_row A x i

example {m n : ℕ} (A : Mat m n) (x : Space n) (hx : ‖x‖ = 1) :
    inner ℝ (covarianceOperator A x) x =
      (∑ i, directionalEnergy x (matrixRow A i)) / m - 1 := by
  exact covariance_quadratic_rows A x hx

example {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (X : Fin m → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) (a : ℝ)
    (hmgf : ∀ i, mgf (X i) μ a ≤ Real.exp (32 * a ^ 2)) :
    mgf (fun ω => ∑ i, X i ω) μ a ≤ Real.exp (32 * (m : ℝ) * a ^ 2) := by
  exact independent_mgf_sum_bound μ X hX hind a hmgf

example {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    (X : Fin m → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ (a : ℝ), |a| ≤ 1 / 8 → ∀ i,
      Integrable (fun ω => Real.exp (a * X i ω)) μ ∧
      mgf (X i) μ a ≤ Real.exp (32 * a ^ 2))
    (s : ℝ) (hs : 0 < s ∧ s ≤ 1) :
    μ.real {ω | s < |(∑ i, X i ω) / m|} ≤
      2 * Real.exp (-(m : ℝ) * s ^ 2 / 128) := by
  exact independent_mgf_average_tail μ hm X hX hind hmgf s hs

example (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1)
    (hmgf : ∀ a : ℝ, |a| ≤ 1 / 8 →
      Integrable (fun u => Real.exp (a * (directionalEnergy x u - 1))) (sphereLaw n) ∧
      (∫ u, Real.exp (a * (directionalEnergy x u - 1)) ∂sphereLaw n) ≤
        Real.exp (32 * a ^ 2))
    (s : ℝ) (hs : 0 < s ∧ s ≤ 1) :
    (matrixLaw m n).real {A | s < |inner ℝ (covarianceOperator A x) x|} ≤
      2 * Real.exp (-(m : ℝ) * s ^ 2 / 128) := by
  exact directional_quadratic_tail_of_mgf m n hm hn x hx hmgf s hs

example (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (hmgf : ∀ (x : Space n), ‖x‖ = 1 → ∀ a : ℝ, |a| ≤ 1 / 8 →
      Integrable (fun u => Real.exp (a * (directionalEnergy x u - 1))) (sphereLaw n) ∧
      (∫ u, Real.exp (a * (directionalEnergy x u - 1)) ∂sphereLaw n) ≤
        Real.exp (32 * a ^ 2))
    (t : ℝ) (ht : 0 < t ∧ t ≤ 1) :
    (matrixLaw m n).real {A | covarianceError A > t} ≤
      2 * (9 : ℝ) ^ n * Real.exp (-(m : ℝ) * t ^ 2 / 512) := by
  exact covariance_concentration_of_mgf m n hm hn hmgf t ht

example (u v h e t : ℝ) (hh : 0 ≤ h ∧ h ≤ 1)
    (hu : |u - h| ≤ e) (hv : |v - 1| ≤ t) (ht : t < 1) :
    0 < v ∧ |u / v - h| ≤ (e + t) / (1 - t) := by
  exact ratio_stability u v h e t hh hu hv ht

example {m n : ℕ} (θ : ℝ) (A : Mat m n)
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    deletionRatio θ A = normalizedDeletion θ A / normalizedOperator A := by
  exact deletionRatio_eq_normalized θ A hm hn

end NLA.IE21
