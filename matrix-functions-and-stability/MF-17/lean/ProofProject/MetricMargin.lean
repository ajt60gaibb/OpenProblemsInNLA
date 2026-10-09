import ProofProject.Definitions

/-!
# Exact-M margin by perturbing an energy

This is the algebraic metric argument in the lower-bound construction. The old
and new energies are explicit functions, so there are no competing norm or
inner-product instances. `BasisEnergy` supplies the two comparison inequalities
for a unit basis with bounded tail projections.
-/

noncomputable section

namespace ProofProject

/-- The Euclidean perturbation size for a model with `N` coordinates. -/
def metricEta (M : ℝ) (N : ℕ) : ℝ := 1 / (4 * M ^ 2 * N)

/-- The squared operator-norm margin produced by the perturbation. -/
def metricGamma (M : ℝ) (N : ℕ) : ℝ := (M ^ 2 - 1) / (4 * M ^ 2 * (N : ℝ) ^ 2 + 1)

/-- Keep the original and perturbed energies explicitly distinct. -/
def perturbedEnergy {E : Type*} (η : ℝ) (q q₀ : E → ℝ) (x : E) : ℝ :=
  q x + η * q₀ x

lemma metricEta_pos {M : ℝ} {N : ℕ} (hM : 1 < M) (hN : 0 < N) :
    0 < metricEta M N := by
  unfold metricEta
  positivity

lemma metricGamma_pos {M : ℝ} {N : ℕ} (hM : 1 < M) :
    0 < metricGamma M N := by
  have hsq : 0 < M ^ 2 - 1 := by nlinarith
  exact div_pos hsq (by positivity)

lemma metricGamma_le {M : ℝ} {N : ℕ} (hM : 1 < M) :
    metricGamma M N ≤ M ^ 2 - 1 := by
  unfold metricGamma
  apply (div_le_iff₀ (by positivity : 0 < 4 * M ^ 2 * (N : ℝ) ^ 2 + 1)).mpr
  have ha : 0 ≤ M ^ 2 - 1 := by nlinarith
  nlinarith [mul_nonneg ha (show 0 ≤ 4 * M ^ 2 * (N : ℝ) ^ 2 by positivity)]

lemma metricGamma_eq {M : ℝ} {N : ℕ} (hM : 1 < M) (hN : 0 < N) :
    metricGamma M N = (M ^ 2 - 1) * metricEta M N / ((N : ℝ) + metricEta M N) := by
  have hM0 : M ≠ 0 := by linarith
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  unfold metricGamma metricEta
  field_simp

/-- The positive margin has the precise inverse-square order in the dimension. -/
lemma metricGamma_lower {M : ℝ} {N : ℕ} (hM : 1 < M) (hN : 0 < N) :
    ((M ^ 2 - 1) / (4 * M ^ 2 + 1)) / (N : ℝ) ^ 2 ≤ metricGamma M N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnum : 0 ≤ M ^ 2 - 1 := by nlinarith
  have hden : 0 < 4 * M ^ 2 * (N : ℝ) ^ 2 + 1 := by positivity
  rw [div_div, metricGamma]
  apply div_le_div_of_nonneg_left hnum hden
  nlinarith

/-- The new norm bound remains at least one, including the identity pattern. -/
lemma one_le_metricMargin_sq {M : ℝ} {N : ℕ} (hM : 1 < M) :
    1 ≤ M ^ 2 - metricGamma M N := by
  linarith [metricGamma_le (N := N) hM]

section Energy

variable {E : Type*} {M : ℝ} {N : ℕ} {q q₀ : E → ℝ}

/-- Adding a nonnegative Euclidean energy can only increase the energy. -/
lemma le_perturbedEnergy (hM : 1 < M) (hN : 0 < N)
    (hq₀ : ∀ x, 0 ≤ q₀ x) (x : E) :
    q x ≤ perturbedEnergy (metricEta M N) q q₀ x := by
  exact le_add_of_nonneg_right (mul_nonneg (metricEta_pos hM hN).le (hq₀ x))

/-- Coordinate projection bounds limit the distortion to a factor two in energy. -/
lemma perturbedEnergy_le_twice (hM : 1 < M) (hN : 0 < N)
    (hlower : ∀ x, q₀ x ≤ 4 * M ^ 2 * N * q x) (x : E) :
    perturbedEnergy (metricEta M N) q q₀ x ≤ 2 * q x := by
  have hη := metricEta_pos hM hN
  have hcancel : metricEta M N * (4 * M ^ 2 * N) = 1 := by
    unfold metricEta
    exact one_div_mul_cancel (ne_of_gt (by positivity))
  have h := mul_le_mul_of_nonneg_left (hlower x) hη.le
  rw [← mul_assoc, hcancel, one_mul] at h
  unfold perturbedEnergy
  linarith

lemma perturbedEnergy_le_euclidean (hupper : ∀ x, q x ≤ (N : ℝ) * q₀ x) (x : E) :
    perturbedEnergy (metricEta M N) q q₀ x ≤ ((N : ℝ) + metricEta M N) * q₀ x := by
  unfold perturbedEnergy
  nlinarith [hupper x]

/-- A simultaneous M-bound in the original metric and contraction in the
Euclidean metric produces the strictly smaller squared bound M²-γ. -/
theorem perturbedEnergy_contraction (hM : 1 < M) (hN : 0 < N)
    (hupper : ∀ x, q x ≤ (N : ℝ) * q₀ x)
    (D : E → E) (hD : ∀ x, q (D x) ≤ M ^ 2 * q x)
    (hD₀ : ∀ x, q₀ (D x) ≤ q₀ x) (x : E) :
    perturbedEnergy (metricEta M N) q q₀ (D x) ≤
      (M ^ 2 - metricGamma M N) * perturbedEnergy (metricEta M N) q q₀ x := by
  have hη := metricEta_pos hM hN
  have hγ := metricGamma_pos (N := N) hM
  have hnη : 0 < (N : ℝ) + metricEta M N := by positivity
  have hidentity : metricGamma M N * ((N : ℝ) + metricEta M N) =
      (M ^ 2 - 1) * metricEta M N := by
    rw [metricGamma_eq hM hN, div_mul_cancel₀ _ hnη.ne']
  have hcomp := mul_le_mul_of_nonneg_left (perturbedEnergy_le_euclidean (M := M) hupper x) hγ.le
  rw [← mul_assoc, hidentity] at hcomp
  have hDη := mul_le_mul_of_nonneg_left (hD₀ x) hη.le
  unfold perturbedEnergy at *
  nlinarith [hD x]

/-- A pointwise squared-gain witness loses at most a factor two under the
perturbation. This avoids asserting that an operator norm is attained. -/
theorem perturbedEnergy_preserves_gain (hM : 1 < M) (hN : 0 < N)
    (hq₀ : ∀ x, 0 ≤ q₀ x) (hlower : ∀ x, q₀ x ≤ 4 * M ^ 2 * N * q x)
    (S : E → E) {a : ℝ} (ha : 0 ≤ a) {x : E} (hx : a * q x ≤ q (S x)) :
    (a / 2) * perturbedEnergy (metricEta M N) q q₀ x ≤
      perturbedEnergy (metricEta M N) q q₀ (S x) := by
  have hi := le_perturbedEnergy (q := q) hM hN hq₀ (S x)
  have ho := mul_le_mul_of_nonneg_left (perturbedEnergy_le_twice hM hN hlower x) ha
  nlinarith

/-- Taking square roots gives the norm form of the strict pattern bound. -/
theorem sqrt_perturbedEnergy_contraction (hM : 1 < M) (hN : 0 < N)
    (hupper : ∀ x, q x ≤ (N : ℝ) * q₀ x)
    (D : E → E) (hD : ∀ x, q (D x) ≤ M ^ 2 * q x)
    (hD₀ : ∀ x, q₀ (D x) ≤ q₀ x) (x : E) :
    Real.sqrt (perturbedEnergy (metricEta M N) q q₀ (D x)) ≤
      Real.sqrt (M ^ 2 - metricGamma M N) *
        Real.sqrt (perturbedEnergy (metricEta M N) q q₀ x) := by
  have h := Real.sqrt_le_sqrt (perturbedEnergy_contraction hM hN hupper D hD hD₀ x)
  rwa [Real.sqrt_mul (zero_le_one.trans (one_le_metricMargin_sq hM))] at h

end Energy

/-- The margin absorbs an additive error without increasing the fixed bound M. -/
theorem sqrt_margin_absorbs_error {M γ : ℝ} (hM : 0 < M) (hγ : 0 ≤ γ)
    (hγM : γ ≤ M ^ 2) : Real.sqrt (M ^ 2 - γ) + γ / (2 * M) ≤ M := by
  have hden : 0 < 2 * M := by positivity
  have he : 0 ≤ γ / (2 * M) := div_nonneg hγ hden.le
  have hmul : 2 * M * (γ / (2 * M)) = γ := mul_div_cancel₀ _ hden.ne'
  have hhalf : γ / (2 * M) ≤ M / 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hroot : Real.sqrt (M ^ 2 - γ) ≤ M - γ / (2 * M) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [sq_nonneg (γ / (2 * M))]
  linarith

/-- The source's ε=γ/(12M²) makes its approximation error 6Mε admissible. -/
lemma metricMargin_absorbs_source_error {M : ℝ} {N : ℕ} (hM : 1 < M) :
    Real.sqrt (M ^ 2 - metricGamma M N) + 6 * M * (metricGamma M N / (12 * M ^ 2)) ≤ M := by
  have hM0 : 0 < M := by linarith
  have he : 6 * M * (metricGamma M N / (12 * M ^ 2)) = metricGamma M N / (2 * M) := by
    field_simp
    ring
  rw [he]
  exact sqrt_margin_absorbs_error hM0 (metricGamma_pos hM).le
    ((metricGamma_le hM).trans (by linarith))

end ProofProject
