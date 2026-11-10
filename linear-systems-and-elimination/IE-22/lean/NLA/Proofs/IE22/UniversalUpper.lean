import NLA.Proofs.IE22.GaussianUpperBounds
import NLA.Proofs.IE22.SpectralProjection
import NLA.Proofs.IE22.GaussianUpperRealization
import NLA.Proofs.IE22.UpperParameters

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NLA.Proofs.IE22
open NLA.Statements.RowDeletion

/-- Threshold continuity follows directly from the actual finite dual. -/
theorem gaussianTrimmingDual_threshold_diff_le {m n : ℕ} (hm : 0 < m)
    {θ : ℝ} (hθ1 : θ ≤ 1) (b : Fin m → Euclid n) (g : Euclid n) (t s : ℝ) :
    |gaussianTrimmingDual θ b t g - gaussianTrimmingDual θ b s g| ≤ 2*|t-s| := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hk : ((RetainedCount θ m : ℕ) : ℝ)/(m : ℝ) ≤ 1 := by
    apply (div_le_one hmR).2
    exact_mod_cast retainedCount_le hθ1 m
  have hc : 0 ≤ ((RetainedCount θ m : ℕ) : ℝ)/(m : ℝ) := by positivity
  have hhinge (z : ℝ) : |hinge t z-hinge s z| ≤ |t-s| := by
    have h := (LipschitzWith.id.max_const (0 : ℝ)).dist_le_mul (t-z^2) (s-z^2)
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, hinge,
      sub_sub_sub_cancel_right, id_eq] using h
  have hsum : |∑ i, (hinge t (inner ℝ (b i) g)-hinge s (inner ℝ (b i) g))| ≤
      (m : ℝ)*|t-s| := by
    calc
      _ ≤ ∑ i, |hinge t (inner ℝ (b i) g)-hinge s (inner ℝ (b i) g)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, |t-s| := Finset.sum_le_sum (fun i _ => hhinge _)
      _ = _ := by simp
  have halg : gaussianTrimmingDual θ b t g-gaussianTrimmingDual θ b s g =
      (((RetainedCount θ m : ℕ) : ℝ)/(m : ℝ))*(t-s) -
      (1/(m : ℝ))*∑ i, (hinge t (inner ℝ (b i) g)-hinge s (inner ℝ (b i) g)) := by
    unfold gaussianTrimmingDual
    rw [Finset.sum_sub_distrib]
    ring
  rw [halg]
  calc
    _ ≤ |(((RetainedCount θ m : ℕ) : ℝ)/(m : ℝ))*(t-s)| +
        |(1/(m : ℝ))*∑ i, (hinge t (inner ℝ (b i) g)-hinge s (inner ℝ (b i) g))| := abs_sub _ _
    _ = (((RetainedCount θ m : ℕ) : ℝ)/(m : ℝ))*|t-s| +
        (1/(m : ℝ))*|∑ i, (hinge t (inner ℝ (b i) g)-hinge s (inner ℝ (b i) g))| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg (by positivity : 0 ≤ 1/(m : ℝ))]
    _ ≤ 1*|t-s| + (1/(m : ℝ))*((m : ℝ)*|t-s|) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hk (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = _ := by field_simp [hmR.ne']; ring

/-- A genuine good Gaussian realization produces a genuine original unit
vector and retained row set, yielding the exact normalized energy estimate. -/
theorem subsingular_upper_of_good_gaussian {m n r : ℕ} (hm : 0 < m) (hr : r < n)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (A : Matrix (Fin m) (Fin n) ℝ) (D : SpectralProjectionData A r)
    {δ H : ℝ} (hδ1 : δ < 1) (hH : 0 ≤ H)
    (g : Euclid (n-r))
    (hnorm : (1-δ)*(n-r : ℕ) ≤ ‖g‖^2)
    (henergy : (∑ i, (inner ℝ (WithLp.toLp 2 (D.rows i)) g)^2) ≤ 4*(m : ℝ))
    (hdual : ∀ t : ℝ, 0 ≤ t → t ≤ 4/(1-θ) →
      gaussianTrimmingDual θ (fun i => WithLp.toLp 2 (D.rows i)) t g ≤ H) :
    (n : ℝ)/(m : ℝ)*SubsingularSquared θ A ≤
      (n : ℝ)/((1-δ)*(n-r : ℕ))*H := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdR : (0 : ℝ) < (n-r : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hr)
  have hlow : 0 < (1-δ)*(n-r : ℕ) := mul_pos (sub_pos.mpr hδ1) hdR
  have hgpos : 0 < ‖g‖ := by nlinarith [norm_nonneg g]
  let b : Fin m → Euclid (n-r) := fun i => WithLp.toLp 2 (D.rows i)
  obtain ⟨S,t,hS,ht0,htL,heq⟩ := exists_bounded_trimming_cut hm hθ0 hθ1
    (fun i => (inner ℝ (b i) g)^2) (fun i => sq_nonneg _) henergy
  have hpsi := hdual t ht0 htL
  have hdualEq : (m : ℝ)*gaussianTrimmingDual θ b t g = ∑ i ∈ S, (inner ℝ (b i) g)^2 := by
    rw [← heq]
    unfold gaussianTrimmingDual
    rw [hS]
    simp only [hinge]
    field_simp [hmR.ne']
    <;> ring
  have hsum : ∑ i ∈ S, (inner ℝ (b i) g)^2 ≤ (m : ℝ)*H := by
    rw [← hdualEq]
    exact mul_le_mul_of_nonneg_left hpsi hmR.le
  let x : Fin n → ℝ := WithLp.ofLp (D.lift (‖g‖⁻¹ • g))
  have hxNorm : ‖D.lift (‖g‖⁻¹ • g)‖ = 1 := by
    rw [D.lift.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hgpos)]
    exact inv_mul_cancel₀ hgpos.ne'
  have hx : UnitVector x := by
    have h := gaussian_norm_sq_eq_sum (D.lift (‖g‖⁻¹ • g))
    rw [hxNorm] at h
    simpa only [UnitVector, x, one_pow] using h.symm
  have hrow (i : Fin m) : RowValue A i x = ‖g‖⁻¹*inner ℝ (b i) g := by
    change RowValue A i (WithLp.ofLp (D.lift (‖g‖⁻¹ • g))) = _
    rw [D.row_eq]
    simp only [inner_smul_right]
    rfl
  have hvalue : ∑ i ∈ S, (RowValue A i x)^2 =
      (‖g‖⁻¹)^2 * ∑ i ∈ S, (inner ℝ (b i) g)^2 := by
    simp only [hrow, mul_pow, Finset.mul_sum]
  have hmin := subsingularSquared_le_energy A S hS x hx
  rw [hvalue] at hmin
  calc
    _ ≤ (n : ℝ)/(m : ℝ)*((‖g‖⁻¹)^2*∑ i ∈ S, (inner ℝ (b i) g)^2) :=
      mul_le_mul_of_nonneg_left hmin (by positivity)
    _ ≤ (n : ℝ)/(m : ℝ)*((‖g‖⁻¹)^2*((m : ℝ)*H)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)) (by positivity)
    _ = (n : ℝ)/‖g‖^2*H := by field_simp [hmR.ne', hgpos.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hlow hnorm) hH

/-- A squared universal upper bound, uniform in every positive row count.
Only the ambient dimension threshold depends on the requested error. -/
theorem uniform_squared_upper (θ a : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 < a)
    (hquantile : GaussianQuantile θ a) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n m : ℕ, 0 < n → 0 < m → N ≤ n →
        ∀ A : Matrix (Fin m) (Fin n) ℝ, UnitRows A →
          (n : ℝ) / (m : ℝ) * SubsingularSquared θ A ≤ TrimmedMoment a + ε := by
  classical
  intro ε hε
  let L := 4/(1-θ)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨δ,hδ,hδ1,hparameters⟩ := exists_upper_parameters ε hε L normalSquareVariance hL
    normalSquareVariance_nonneg
  obtain ⟨T,hTsub,hTfinite,hTcover⟩ := isCompact_Icc.finite_cover_balls (s := Set.Icc (0 : ℝ) L) hδ
  let F := hTfinite.toFinset
  have hF : ∀ t ∈ F, 0 ≤ t ∧ t ≤ L := by
    intro t ht
    exact hTsub (hTfinite.mem_toFinset.mp ht)
  obtain ⟨r,N,hN⟩ := hparameters F.card
  refine ⟨N,?_⟩
  intro n m _hn hm hnN A hA
  obtain ⟨hr,hprob,hinflate⟩ := hN n hnN
  obtain ⟨D⟩ := exists_spectral_projection hr A hA
  let b : Fin m → Euclid (n-r) := fun i => WithLp.toLp 2 (D.rows i)
  have hd : 0 < n-r := Nat.sub_pos_of_lt hr
  obtain ⟨g,hnorm,henergy,hgrid⟩ := exists_good_gaussian hm hd hθ0.le ha.le hquantile
    b D.row_norm_sq D.gram_sum δ hδ hδ1 L hL F hF hprob
  have hall : ∀ t : ℝ, 0 ≤ t → t ≤ L →
      gaussianTrimmingDual θ b t g ≤ TrimmedMoment a+3*δ := by
    intro t ht0 htL
    have ht := hTcover ⟨ht0,htL⟩
    obtain ⟨s,hsT,hst⟩ := Set.mem_iUnion₂.mp ht
    have hsF : s ∈ F := hTfinite.mem_toFinset.mpr hsT
    have hdist : |t-s| < δ := by simpa only [Metric.mem_ball, Real.dist_eq] using hst
    have hdif := gaussianTrimmingDual_threshold_diff_le hm hθ1.le b g t s
    have hle := le_abs_self (gaussianTrimmingDual θ b t g-gaussianTrimmingDual θ b s g)
    have hsg := hgrid s hsF
    linarith
  have hmoment0 := trimmedMoment_nonneg ha.le
  have hmoment1 := trimmedMoment_le_one ha.le
  have hbound := subsingular_upper_of_good_gaussian hm hr hθ0.le hθ1 A D hδ1
    (by positivity : 0 ≤ TrimmedMoment a+3*δ) g hnorm henergy hall
  exact hbound.trans (hinflate (TrimmedMoment a) hmoment0 hmoment1)

#assert_trust kernel uniform_squared_upper
#print axioms uniform_squared_upper
#assert_trust kernel gaussianTrimmingDual_threshold_diff_le
#assert_trust kernel subsingular_upper_of_good_gaussian
#print axioms subsingular_upper_of_good_gaussian
end NLA.Proofs.IE22
