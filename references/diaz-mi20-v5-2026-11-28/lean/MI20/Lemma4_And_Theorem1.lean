/-
  MI20/Lemma4_And_Theorem1.lean
  =============================
  Author: Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
  Löwner–Heinz monotonicity, Lemma 4(a)–(b), Proposition 5 (superquadratic obstruction), and Theorem 1 (strict infinite-dimensional hierarchy).
-/

import MI20.Lemma2_LeftRotation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section

namespace MI20

/-! ### Convenience Lemmas for Schatten Norms and Lee Constants -/

lemma schattenNorm_rpow {n : ℕ} {p : ℝ} (hp : 0 < p) (A : Mat n) :
    (schattenNorm p A) ^ p = schattenPow p A := by
  unfold schattenNorm
  rw [one_div]
  exact Real.rpow_inv_rpow (schattenPow_nonneg p A) hp.ne'

lemma schattenNorm_pos_of_ne_zero {n : ℕ} {p : ℝ} (hp : 0 < p) {A : Mat n} (hA : A ≠ 0) :
    0 < schattenNorm p A :=
  (schattenNorm_pos_iff hp A).mpr hA

lemma leeConst_bddAbove {m n : ℕ} {p : ℝ} (hp : 1 < p) :
    BddAbove { r : ℝ | ∃ A : Fin m → Mat n, (∑ k, matAbs (A k)) ≠ 0 ∧ r = leeRatio p A } := by
  refine ⟨(m : ℝ), ?_⟩
  rintro _ ⟨A, _, rfl⟩
  exact leeRatio_le_card hp A

/-! ### PSD Real Powers H^q via Continuous Functional Calculus -/

/-- For a positive semidefinite matrix H and exponent q > 0, define H^q := cfc (fun x => x ^ q) H. -/
def psdPow (q : ℝ) {n : ℕ} (H : Mat n) : Mat n :=
  cfc (fun x : ℝ => x ^ q) H

lemma psdPow_eq_spectral {n : ℕ} {q : ℝ} (_hq : 0 < q) {H : Mat n} (hH : H.PosSemidef) :
    psdPow q H = (hH.isHermitian.eigenvectorUnitary : Mat n) *
      Matrix.diagonal (fun i => (((hH.isHermitian.eigenvalues i) ^ q : ℝ) : ℂ)) *
      (hH.isHermitian.eigenvectorUnitary : Mat n)ᴴ := by
  rw [psdPow, hH.isHermitian.cfc_eq]
  simp [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Function.comp_def]

lemma psdPow_posSemidef {n : ℕ} {q : ℝ} (hq : 0 < q) {H : Mat n} (hH : H.PosSemidef) :
    (psdPow q H).PosSemidef := by
  rw [psdPow_eq_spectral hq hH]
  have hd : (Matrix.diagonal (fun i => (((hH.isHermitian.eigenvalues i) ^ q : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i; exact_mod_cast Real.rpow_nonneg (hH.eigenvalues_nonneg i) q
  simpa using hd.mul_mul_conjTranspose_same (hH.isHermitian.eigenvectorUnitary : Mat n)

lemma psdPow_unitary_conj {n : ℕ} {q : ℝ} (hq : 0 < q)
    (U : Matrix.unitaryGroup (Fin n) ℂ) {H : Mat n} (hH : H.PosSemidef) :
    psdPow q ((U : Mat n) * H * (U : Mat n)ᴴ) = (U : Mat n) * psdPow q H * (U : Mat n)ᴴ :=
  cfc_conj_unitary U hH.isHermitian (Real.continuous_rpow_const hq.le).continuousOn

lemma psdPow_diagonal {n : ℕ} {q : ℝ} (_hq : 0 < q) (d : Fin n → ℝ) :
    psdPow q (Matrix.diagonal (fun i => (d i : ℂ))) =
      Matrix.diagonal (fun i => (((d i) ^ q : ℝ) : ℂ)) :=
  cfc_diagonal_real d (fun x : ℝ => x ^ q)

lemma psdPow_padZero {n : ℕ} {q : ℝ} (hq : 0 < q) {H : Mat n} (hH : H.PosSemidef) :
    psdPow q (padZero H) = padZero (psdPow q H) := by
  let U := hH.isHermitian.eigenvectorUnitary
  let lam := hH.isHermitian.eigenvalues
  have hH_eq : H = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hH.isHermitian.spectral_theorem
  let lamExt : Fin (n + 1) → ℝ := fun i => if hi : i.val < n then lam ⟨i.val, hi⟩ else 0
  have hDiag : padZero (Matrix.diagonal (fun i => (lam i : ℂ))) =
      Matrix.diagonal (fun i => (lamExt i : ℂ)) := by
    rw [padZero_diagonal]; congr 1; ext i; dsimp [lamExt]; split_ifs <;> simp
  have hpadH : padZero H = (padUnitary U : Mat (n + 1)) * Matrix.diagonal (fun i => (lamExt i : ℂ)) *
      (padUnitary U : Mat (n + 1))ᴴ := by
    rw [hH_eq, ← padZero_mul_padUnitary_conjTranspose, ← padUnitary_mul_padZero, hDiag]
  have hD_psd : (Matrix.diagonal (fun i => (lamExt i : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro i; dsimp [lamExt]
    split_ifs
    · exact_mod_cast hH.eigenvalues_nonneg _
    · exact_mod_cast le_rfl
  rw [hpadH, psdPow_unitary_conj hq (padUnitary U) hD_psd, psdPow_diagonal hq lamExt,
    psdPow_eq_spectral hq hH, ← padZero_mul_padUnitary_conjTranspose, ← padUnitary_mul_padZero,
    padZero_diagonal]
  congr 2; congr 1; ext i; dsimp [lamExt]
  by_cases hi : i.val < n
  · simp [lam, hi]
  · simp [hi, Real.zero_rpow hq.ne']

lemma psdPow_add_smul_one {n : ℕ} {q : ℝ} (hq : 0 < q) {H : Mat n} (hH : H.PosSemidef) (δ : ℝ)
    (hδ : 0 ≤ δ) :
    psdPow q (H + (δ : ℂ) • (1 : Mat n)) =
      (hH.isHermitian.eigenvectorUnitary : Mat n) *
        Matrix.diagonal (fun i => (((hH.isHermitian.eigenvalues i + δ) ^ q : ℝ) : ℂ)) *
        (hH.isHermitian.eigenvectorUnitary : Mat n)ᴴ := by
  let U := hH.isHermitian.eigenvectorUnitary
  let lam := hH.isHermitian.eigenvalues
  have hH_eq : H = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hH.isHermitian.spectral_theorem
  have hEq : H + (δ : ℂ) • (1 : Mat n) =
      (U : Mat n) * Matrix.diagonal (fun i => ((lam i + δ : ℝ) : ℂ)) * (U : Mat n)ᴴ := by
    have h1 : (δ : ℂ) • (1 : Mat n) = (U : Mat n) * Matrix.diagonal (fun _ => (δ : ℂ)) * (U : Mat n)ᴴ := by
      have hd : Matrix.diagonal (fun _ : Fin n => (δ : ℂ)) = (δ : ℂ) • (1 : Mat n) := by
        ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
      rw [hd, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, unitary_mul_conjTranspose_self U]
    rw [hH_eq, h1, ← Matrix.add_mul, ← Matrix.mul_add]
    congr 2; ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have hD_psd : (Matrix.diagonal (fun i => ((lam i + δ : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro i
    exact_mod_cast add_nonneg (hH.eigenvalues_nonneg i) hδ
  rw [hEq, psdPow_unitary_conj hq U hD_psd, psdPow_diagonal hq (fun i => lam i + δ)]

/-! ### Doubly-Stochastic Parseval Second-Order Bound & Derivative of (1/p) ‖X + h E‖_p^p -/

/-- Scalar C² Taylor bound via MVT twice:
    for p > 1 and a, b ∈ [lo, hi] (with lo > 0 if p < 2, or lo ≥ 0 if p ≥ 2),
    |b^p/p - a^p/p - a^(p-1) * (b - a)| ≤ K * (b - a)^2
    where K = (p - 1) * max(lo^(p-2), hi^(p-2)) (or (p-1)*hi^(p-2) for p ≥ 2). -/
lemma scalar_rpow_taylor_bound {p lo hi K : ℝ} (hp : 1 < p) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (hK : ∀ c ∈ Set.Icc lo hi, |(p - 1) * c ^ (p - 2)| ≤ K)
    (_hpos_or_ge2 : 0 < lo ∨ 2 ≤ p)
    {a b : ℝ} (ha : a ∈ Set.Icc lo hi) (hb : b ∈ Set.Icc lo hi) :
    |(1 / p) * b ^ p - (1 / p) * a ^ p - a ^ (p - 1) * (b - a)| ≤ K * (b - a) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hK_nn : 0 ≤ K := (abs_nonneg _).trans (hK lo ⟨le_rfl, hlohi⟩)
  by_cases hab : a = b
  · subst hab; simp
  -- WLOG let u = min a b < v = max a b; apply MVT to g(x) = x^p / p - a^p / p - a^(p-1)*(x - a)
  let g : ℝ → ℝ := fun x => (1 / p) * x ^ p - (1 / p) * a ^ p - a ^ (p - 1) * (x - a)
  have hg_deriv : ∀ x : ℝ, 0 ≤ x → HasDerivAt g (x ^ (p - 1) - a ^ (p - 1)) x := by
    intro x hx
    have hrp : HasDerivAt (fun t : ℝ => t ^ p) (p * x ^ (p - 1)) x := by
      simpa using Real.hasDerivAt_rpow_const (p := p) (x := x) (Or.inr hp.le)
    have h1 : HasDerivAt (fun t : ℝ => (1 / p) * t ^ p) (x ^ (p - 1)) x := by
      have := hrp.const_mul (1 / p)
      have hsimp : (1 / p) * (p * x ^ (p - 1)) = x ^ (p - 1) := by field_simp [hp0.ne']
      rwa [hsimp] at this
    have h2 : HasDerivAt (fun t : ℝ => (1 / p) * t ^ p - (1 / p) * a ^ p) (x ^ (p - 1)) x :=
      h1.sub_const _
    have h3 : HasDerivAt (fun t : ℝ => a ^ (p - 1) * (t - a)) (a ^ (p - 1)) x := by
      simpa using ((hasDerivAt_id x).sub_const a).const_mul (a ^ (p - 1))
    exact h2.sub h3
  have hpm1_deriv : ∀ x ∈ Set.Ioo lo hi, HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * x ^ (p - 2)) x := by
    intro x hx
    have hx_pos : 0 < x := lt_of_le_of_lt hlo hx.1
    have h1 := Real.hasDerivAt_rpow_const (p := p - 1) (x := x) (Or.inl hx_pos.ne')
    have hsub : p - 1 - 1 = p - 2 := by ring
    simpa [hsub] using h1
  have hlip : ∀ c ∈ Set.Icc lo hi, |c ^ (p - 1) - a ^ (p - 1)| ≤ K * |c - a| := by
    intro c hc
    by_cases hca : c = a
    · subst hca; simp
    · rcases lt_or_gt_of_ne hca with hlt | hgt
      · have hcont : ContinuousOn (fun t : ℝ => t ^ (p - 1)) (Set.Icc c a) :=
          (Real.continuous_rpow_const (by linarith)).continuousOn
        have hdiff : ∀ x ∈ Set.Ioo c a, HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * x ^ (p - 2)) x :=
          fun x hx => hpm1_deriv x ⟨lt_of_le_of_lt hc.1 hx.1, lt_of_lt_of_le hx.2 ha.2⟩
        obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (p - 1)) _ hlt hcont hdiff
        have hξ_mem : ξ ∈ Set.Icc lo hi := ⟨hc.1.trans hξ.1.le, hξ.2.le.trans ha.2⟩
        have hdiff_eq : a ^ (p - 1) - c ^ (p - 1) = ((p - 1) * ξ ^ (p - 2)) * (a - c) := by
          rw [eq_div_iff (sub_pos.mpr hlt).ne'] at hslope; exact hslope.symm
        calc |c ^ (p - 1) - a ^ (p - 1)|
            = |a ^ (p - 1) - c ^ (p - 1)| := abs_sub_comm _ _
          _ = |(p - 1) * ξ ^ (p - 2)| * |a - c| := by rw [hdiff_eq, abs_mul]
          _ ≤ K * |a - c| := mul_le_mul_of_nonneg_right (hK ξ hξ_mem) (abs_nonneg _)
          _ = K * |c - a| := by rw [abs_sub_comm]
      · have hcont : ContinuousOn (fun t : ℝ => t ^ (p - 1)) (Set.Icc a c) :=
          (Real.continuous_rpow_const (by linarith)).continuousOn
        have hdiff : ∀ x ∈ Set.Ioo a c, HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * x ^ (p - 2)) x :=
          fun x hx => hpm1_deriv x ⟨lt_of_le_of_lt ha.1 hx.1, lt_of_lt_of_le hx.2 hc.2⟩
        obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (p - 1)) _ hgt hcont hdiff
        have hξ_mem : ξ ∈ Set.Icc lo hi := ⟨ha.1.trans hξ.1.le, hξ.2.le.trans hc.2⟩
        have hdiff_eq : c ^ (p - 1) - a ^ (p - 1) = ((p - 1) * ξ ^ (p - 2)) * (c - a) := by
          rw [eq_div_iff (sub_pos.mpr hgt).ne'] at hslope; exact hslope.symm
        calc |c ^ (p - 1) - a ^ (p - 1)|
            = |(p - 1) * ξ ^ (p - 2)| * |c - a| := by rw [hdiff_eq, abs_mul]
          _ ≤ K * |c - a| := mul_le_mul_of_nonneg_right (hK ξ hξ_mem) (abs_nonneg _)
  -- Apply MVT to g between a and b
  have hg_cont : Continuous g := by
    have h1 : Continuous (fun t : ℝ => (1 / p) * t ^ p) :=
      continuous_const.mul (Real.continuous_rpow_const hp0.le)
    exact (h1.sub continuous_const).sub (continuous_const.mul (continuous_id.sub continuous_const))
  have hga : g a = 0 := by simp [g]
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g _ hlt hg_cont.continuousOn
      (fun x hx => hg_deriv x (hlo.trans (ha.1.trans hx.1.le)))
    have hgb : g b = (c ^ (p - 1) - a ^ (p - 1)) * (b - a) := by
      rw [hga, sub_zero, eq_div_iff (sub_pos.mpr hlt).ne'] at hslope; exact hslope.symm
    have hc_mem : c ∈ Set.Icc lo hi := ⟨ha.1.trans hc.1.le, hc.2.le.trans hb.2⟩
    have hca_le : |c - a| ≤ |b - a| := by
      rw [abs_of_pos (sub_pos.mpr hc.1), abs_of_pos (sub_pos.mpr hlt)]; linarith [hc.2]
    change |g b| ≤ K * (b - a) ^ 2
    rw [hgb, abs_mul]
    calc |c ^ (p - 1) - a ^ (p - 1)| * |b - a|
        ≤ (K * |c - a|) * |b - a| := mul_le_mul_of_nonneg_right (hlip c hc_mem) (abs_nonneg _)
      _ ≤ (K * |b - a|) * |b - a| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hca_le hK_nn) (abs_nonneg _)
      _ = K * (b - a) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g _ hgt hg_cont.continuousOn
      (fun x hx => hg_deriv x (hlo.trans (hb.1.trans hx.1.le)))
    have hgb : -g b = (c ^ (p - 1) - a ^ (p - 1)) * (a - b) := by
      rw [hga, zero_sub, eq_div_iff (sub_pos.mpr hgt).ne'] at hslope; exact hslope.symm
    have hc_mem : c ∈ Set.Icc lo hi := ⟨hb.1.trans hc.1.le, hc.2.le.trans ha.2⟩
    have hca_le : |c - a| ≤ |b - a| := by
      rw [abs_of_neg (sub_neg.mpr hc.2), abs_of_neg (sub_neg.mpr hgt)]; linarith [hc.1]
    change |g b| ≤ K * (b - a) ^ 2
    rw [← abs_neg, hgb, abs_mul, abs_sub_comm a b]
    calc |c ^ (p - 1) - a ^ (p - 1)| * |b - a|
        ≤ (K * |c - a|) * |b - a| := mul_le_mul_of_nonneg_right (hlip c hc_mem) (abs_nonneg _)
      _ ≤ (K * |b - a|) * |b - a| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hca_le hK_nn) (abs_nonneg _)
      _ = K * (b - a) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- Matrix second-order Taylor bound via doubly-stochastic Parseval:
    for PSD X, Y whose eigenvalues lie in [lo, hi],
    |(1/p) ‖Y‖_p^p - (1/p) ‖X‖_p^p - Re Tr(X^(p-1) (Y - X))| ≤ K * Re Tr((Y - X)^2)! -/
theorem matrix_schattenPow_taylor_bound {n : ℕ} {p lo hi K : ℝ} (hp : 1 < p)
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (hK : ∀ c ∈ Set.Icc lo hi, |(p - 1) * c ^ (p - 2)| ≤ K)
    (hpos_or_ge2 : 0 < lo ∨ 2 ≤ p)
    {X Y : Mat n} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hX_eig : ∀ i, hX.isHermitian.eigenvalues i ∈ Set.Icc lo hi)
    (hY_eig : ∀ j, hY.isHermitian.eigenvalues j ∈ Set.Icc lo hi) :
    |(1 / p) * schattenPow p Y - (1 / p) * schattenPow p X -
        (psdPow (p - 1) X * (Y - X)).trace.re| ≤
      K * ((Y - X) * (Y - X)).trace.re := by
  have hp0 : 0 < p := by linarith
  have hpm1 : 0 < p - 1 := by linarith
  let Ux := hX.isHermitian.eigenvectorUnitary
  let lam := hX.isHermitian.eigenvalues
  let Uy := hY.isHermitian.eigenvectorUnitary
  let mu := hY.isHermitian.eigenvalues
  have hX_eq : X = (Ux : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (Ux : Mat n)ᴴ := by
    simpa [Ux, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hX.isHermitian.spectral_theorem
  have hY_eq : Y = (Uy : Mat n) * Matrix.diagonal (fun j => (mu j : ℂ)) * (Uy : Mat n)ᴴ := by
    simpa [Uy, mu, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hY.isHermitian.spectral_theorem
  have hPowX : schattenPow p X = ∑ i : Fin n, (lam i) ^ p := by
    rw [hX_eq, schattenPow_unitary_mul_conjTranspose_right hp0.le, schattenPow_unitary_mul_left,
      schattenPow_diagonal hp0 lam hX.eigenvalues_nonneg]
  have hPowY : schattenPow p Y = ∑ j : Fin n, (mu j) ^ p := by
    rw [hY_eq, schattenPow_unitary_mul_conjTranspose_right hp0.le, schattenPow_unitary_mul_left,
      schattenPow_diagonal hp0 mu hY.eigenvalues_nonneg]
  let Qu : Matrix.unitaryGroup (Fin n) ℂ := star Ux * Uy
  let Q : Mat n := (Qu : Mat n)
  have hRowQ : ∀ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 = 1 := by
    intro i
    have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self Qu) i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]; refine Finset.sum_congr rfl fun j _ => ?_
    change ‖Q i j‖ ^ 2 = (Q i j * star (Q i j)).re
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hColQ : ∀ j : Fin n, ∑ i : Fin n, ‖Q i j‖ ^ 2 = 1 := by
    intro j
    have hU := congr_fun (congr_fun (unitary_conjTranspose_mul_self Qu) j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]; refine Finset.sum_congr rfl fun i _ => ?_
    change ‖Q i j‖ ^ 2 = (star (Q i j) * Q i j).re
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  -- Helper: Re Tr(Ux diag(f) Uxᴴ * Uy diag(g) Uyᴴ) = ∑ i j, ‖Q i j‖^2 * f i * g j
  have htr_cross : ∀ (f g : Fin n → ℝ),
      (((Ux : Mat n) * Matrix.diagonal (fun i => (f i : ℂ)) * (Ux : Mat n)ᴴ) *
       ((Uy : Mat n) * Matrix.diagonal (fun j => (g j : ℂ)) * (Uy : Mat n)ᴴ)).trace.re =
      ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * (f i * g j) := by
    intro f g
    have hQeq : (Ux : Mat n)ᴴ * (Uy : Mat n) = Q := rfl
    have hQHeq : (Uy : Mat n)ᴴ * (Ux : Mat n) = Qᴴ := by
      change (Uy : Mat n)ᴴ * (Ux : Mat n) = ((Ux : Mat n)ᴴ * (Uy : Mat n))ᴴ
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    set DF : Mat n := Matrix.diagonal (fun i => (f i : ℂ))
    set DG : Mat n := Matrix.diagonal (fun j => (g j : ℂ))
    have hprod : (((Ux : Mat n) * DF * (Ux : Mat n)ᴴ) * ((Uy : Mat n) * DG * (Uy : Mat n)ᴴ)).trace =
        ((DF * Q) * (DG * Qᴴ)).trace := by
      calc (((Ux : Mat n) * DF * (Ux : Mat n)ᴴ) * ((Uy : Mat n) * DG * (Uy : Mat n)ᴴ)).trace
          = ((Ux : Mat n) * (DF * ((Ux : Mat n)ᴴ * (Uy : Mat n)) * DG * (Uy : Mat n)ᴴ)).trace := by
              congr 1; simp only [Matrix.mul_assoc]
        _ = ((DF * Q * DG * (Uy : Mat n)ᴴ) * (Ux : Mat n)).trace := by
              rw [hQeq, Matrix.trace_mul_comm (Ux : Mat n)]
        _ = ((DF * Q) * (DG * ((Uy : Mat n)ᴴ * (Ux : Mat n)))).trace := by
              congr 1; simp only [Matrix.mul_assoc]
        _ = ((DF * Q) * (DG * Qᴴ)).trace := by rw [hQHeq]
    rw [hprod, Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag, Matrix.mul_apply, DF, DG, Matrix.diagonal_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Matrix.conjTranspose_apply]
    have hmul : ((f i : ℂ) * Q i j * ((g j : ℂ) * star (Q i j))) =
        (((f i * g j : ℝ) : ℂ) * (Q i j * star (Q i j))) := by push_cast; ring
    rw [hmul, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]; ring
  -- Helper: Re Tr(Ux diag(f) Uxᴴ * Ux diag(g) Uxᴴ) = ∑ i, f i * g i
  have htr_same : ∀ (U : Matrix.unitaryGroup (Fin n) ℂ) (f g : Fin n → ℝ),
      (((U : Mat n) * Matrix.diagonal (fun i => (f i : ℂ)) * (U : Mat n)ᴴ) *
       ((U : Mat n) * Matrix.diagonal (fun i => (g i : ℂ)) * (U : Mat n)ᴴ)).trace.re =
      ∑ i : Fin n, f i * g i := by
    intro U f g
    have hprod : ((U : Mat n) * Matrix.diagonal (fun i => (f i : ℂ)) * (U : Mat n)ᴴ) *
        ((U : Mat n) * Matrix.diagonal (fun i => (g i : ℂ)) * (U : Mat n)ᴴ) =
        (U : Mat n) * Matrix.diagonal (fun i => (((f i * g i : ℝ) : ℂ))) * (U : Mat n)ᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n), unitary_conjTranspose_mul_self U,
        Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.diagonal, hij]
    rw [hprod, Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self U, Matrix.one_mul,
      Matrix.trace_diagonal, Complex.re_sum]
    simp
  -- Compute Re Tr(X^(p-1) (Y - X)) = ∑ i j, ‖Q i j‖^2 * lam i^(p-1) * (mu j - lam i)
  have htr_lin : (psdPow (p - 1) X * (Y - X)).trace.re =
      ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * ((lam i) ^ (p - 1) * (mu j - lam i)) := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    have h1 : (psdPow (p - 1) X * Y).trace.re =
        ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * ((lam i) ^ (p - 1) * mu j) := by
      rw [psdPow_eq_spectral hpm1 hX]
      have hY' : ((Ux : Mat n) * Matrix.diagonal (fun i => (((lam i) ^ (p - 1) : ℝ) : ℂ)) * (Ux : Mat n)ᴴ * Y).trace.re =
          (((Ux : Mat n) * Matrix.diagonal (fun i => (((lam i) ^ (p - 1) : ℝ) : ℂ)) * (Ux : Mat n)ᴴ) *
           ((Uy : Mat n) * Matrix.diagonal (fun j => (mu j : ℂ)) * (Uy : Mat n)ᴴ)).trace.re := by
        rw [← hY_eq]
      exact hY'.trans (htr_cross (fun i => (lam i) ^ (p - 1)) mu)
    have h2' : (psdPow (p - 1) X * X).trace.re = ∑ i : Fin n, (lam i) ^ (p - 1) * lam i := by
      rw [psdPow_eq_spectral hpm1 hX]
      have hX' : ((Ux : Mat n) * Matrix.diagonal (fun i => (((lam i) ^ (p - 1) : ℝ) : ℂ)) * (Ux : Mat n)ᴴ * X).trace.re =
          (((Ux : Mat n) * Matrix.diagonal (fun i => (((lam i) ^ (p - 1) : ℝ) : ℂ)) * (Ux : Mat n)ᴴ) *
           ((Ux : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (Ux : Mat n)ᴴ)).trace.re := by
        rw [← hX_eq]
      exact hX'.trans (htr_same Ux (fun i => (lam i) ^ (p - 1)) lam)
    rw [h1, h2']
    have h2 : ∑ i : Fin n, (lam i) ^ (p - 1) * lam i =
        ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * ((lam i) ^ (p - 1) * lam i) := by
      refine Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, hRowQ i, one_mul]
    rw [h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  -- Compute Re Tr((Y - X)^2) = ∑ i j, ‖Q i j‖^2 * (mu j - lam i)^2
  have htr_sq : ((Y - X) * (Y - X)).trace.re =
      ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * (mu j - lam i) ^ 2 := by
    have htr_yx : (Y * X).trace = (X * Y).trace := Matrix.trace_mul_comm Y X
    have hexp : ((Y - X) * (Y - X)).trace.re =
        (Y * Y).trace.re - 2 * (X * Y).trace.re + (X * X).trace.re := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub,
        Matrix.trace_sub, htr_yx, Complex.sub_re, Complex.sub_re, Complex.sub_re]; ring
    rw [hexp]
    have hYY : (Y * Y).trace.re = ∑ j : Fin n, mu j * mu j := by
      have : (Y * Y).trace.re = (((Uy : Mat n) * Matrix.diagonal (fun j => (mu j : ℂ)) * (Uy : Mat n)ᴴ) *
          ((Uy : Mat n) * Matrix.diagonal (fun j => (mu j : ℂ)) * (Uy : Mat n)ᴴ)).trace.re := by
        rw [← hY_eq]
      exact this.trans (htr_same Uy mu mu)
    have hXY : (X * Y).trace.re = ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * (lam i * mu j) := by
      have : (X * Y).trace.re = (((Ux : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (Ux : Mat n)ᴴ) *
          ((Uy : Mat n) * Matrix.diagonal (fun j => (mu j : ℂ)) * (Uy : Mat n)ᴴ)).trace.re := by
        rw [← hX_eq, ← hY_eq]
      exact this.trans (htr_cross lam mu)
    have hXX : (X * X).trace.re = ∑ i : Fin n, lam i * lam i := by
      have : (X * X).trace.re = (((Ux : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (Ux : Mat n)ᴴ) *
          ((Ux : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (Ux : Mat n)ᴴ)).trace.re := by
        rw [← hX_eq]
      exact this.trans (htr_same Ux lam lam)
    rw [hYY, hXY, hXX]
    have hY2 : ∑ j : Fin n, mu j * mu j = ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * (mu j * mu j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hColQ j, one_mul]
    have hX2 : ∑ i : Fin n, lam i * lam i = ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * (lam i * lam i) := by
      refine Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, hRowQ i, one_mul]
    rw [hY2, hX2, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  -- Express LHS as double sum of doubly-stochastic weights times scalar Taylor remainder
  have hlhs : (1 / p) * schattenPow p Y - (1 / p) * schattenPow p X -
      (psdPow (p - 1) X * (Y - X)).trace.re =
      ∑ i : Fin n, ∑ j : Fin n,
        ‖Q i j‖ ^ 2 * ((1 / p) * (mu j) ^ p - (1 / p) * (lam i) ^ p - (lam i) ^ (p - 1) * (mu j - lam i)) := by
    rw [hPowY, hPowX, htr_lin]
    have hYp : (1 / p) * ∑ j : Fin n, (mu j) ^ p =
        ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * ((1 / p) * (mu j) ^ p) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hColQ j, one_mul]
    have hXp : (1 / p) * ∑ i : Fin n, (lam i) ^ p =
        ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * ((1 / p) * (lam i) ^ p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, hRowQ i, one_mul]
    rw [hYp, hXp, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hlhs, htr_sq, Finset.mul_sum]
  calc |∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 *
          ((1 / p) * (mu j) ^ p - (1 / p) * (lam i) ^ p - (lam i) ^ (p - 1) * (mu j - lam i))|
      ≤ ∑ i : Fin n, |∑ j : Fin n, ‖Q i j‖ ^ 2 *
          ((1 / p) * (mu j) ^ p - (1 / p) * (lam i) ^ p - (lam i) ^ (p - 1) * (mu j - lam i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, |‖Q i j‖ ^ 2 *
          ((1 / p) * (mu j) ^ p - (1 / p) * (lam i) ^ p - (lam i) ^ (p - 1) * (mu j - lam i))| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, K * (‖Q i j‖ ^ 2 * (mu j - lam i) ^ 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hsc := scalar_rpow_taylor_bound hp hlo hlohi hK hpos_or_ge2 (hX_eig i) (hY_eig j)
        have := mul_le_mul_of_nonneg_left hsc (sq_nonneg ‖Q i j‖)
        linarith
    _ = ∑ i : Fin n, K * ∑ j : Fin n, ‖Q i j‖ ^ 2 * (mu j - lam i) ^ 2 :=
        Finset.sum_congr rfl fun i _ => (Finset.mul_sum ..).symm

/-- Trace of (M * outerMat v v) equals star v ⬝ᵥ M *ᵥ v. -/
lemma trace_mul_outerMat {n : ℕ} (M : Mat n) (v : Fin n → ℂ) :
    (M * outerMat v v).trace = star v ⬝ᵥ M.mulVec v := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, outerMat, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Eigenvalues of a PSD matrix M bounded above by tr(M) = Re Tr(M). -/
lemma posSemidef_eigenvalues_le_trace {n : ℕ} {M : Mat n} (hM : M.PosSemidef) (i : Fin n) :
    hM.isHermitian.eigenvalues i ≤ M.trace.re := by
  let U := hM.isHermitian.eigenvectorUnitary
  let lam := hM.isHermitian.eigenvalues
  have htr : M.trace.re = ∑ j : Fin n, lam j := by
    have hEq : M = (U : Mat n) * Matrix.diagonal (fun j => (lam j : ℂ)) * (U : Mat n)ᴴ := by
      simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using hM.isHermitian.spectral_theorem
    have htr1 : M.trace = ((U : Mat n) * Matrix.diagonal (fun j => (lam j : ℂ)) * (U : Mat n)ᴴ).trace := by
      rw [← hEq]
    rw [htr1, Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self U, Matrix.one_mul,
      Matrix.trace_diagonal, Complex.re_sum]
    simp
  rw [htr]
  exact Finset.single_le_sum (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- Eigenvalues of M = A + δ I are ≥ δ when A is PSD. -/
lemma posSemidef_add_smul_one_eigenvalues_ge {n : ℕ} {A : Mat n} (hA : A.PosSemidef)
    {δ : ℝ} (_hδ : 0 ≤ δ) (hM : (A + (δ : ℂ) • (1 : Mat n)).PosSemidef) (i : Fin n) :
    δ ≤ hM.isHermitian.eigenvalues i := by
  let b := hM.isHermitian.eigenvectorBasis i
  have hnorm : (star b.ofLp ⬝ᵥ b.ofLp).re = 1 := by
    have h1 := orthonormal_iff_ite.mp hM.isHermitian.eigenvectorBasis.orthonormal i i
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h1
    simpa using congrArg Complex.re h1
  have heig : (star b.ofLp ⬝ᵥ (A + (δ : ℂ) • (1 : Mat n)).mulVec b.ofLp).re =
      hM.isHermitian.eigenvalues i := by
    have h1 := hM.isHermitian.mulVec_eigenvectorBasis i
    change (A + (δ : ℂ) • (1 : Mat n)).mulVec b.ofLp = hM.isHermitian.eigenvalues i • b.ofLp at h1
    rw [h1, dotProduct_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      hnorm]
    ring
  have hge : 0 ≤ (star b.ofLp ⬝ᵥ A.mulVec b.ofLp).re := by
    simpa [RCLike.re_to_complex] using hA.re_dotProduct_nonneg b.ofLp
  have hsplit : (star b.ofLp ⬝ᵥ (A + (δ : ℂ) • (1 : Mat n)).mulVec b.ofLp).re =
      (star b.ofLp ⬝ᵥ A.mulVec b.ofLp).re + δ := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
      Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hnorm]
    ring
  linarith

/-- Derivative of t ↦ (1/p) * schattenPow p (H + δ I + t v vᴴ) for p > 1, δ > 0, unit v, t ≥ 0. -/
theorem hasDerivAt_schattenPow_psd_add_rankOne {n : ℕ} {p δ : ℝ} (hp : 1 < p) (hδ : 0 < δ)
    {H : Mat n} (hH : H.PosSemidef) (v : Fin n → ℂ) (hv : star v ⬝ᵥ v = 1)
    {t0 : ℝ} (ht0 : 0 ≤ t0) :
    HasDerivAt
      (fun t : ℝ => (1 / p) * schattenPow p (H + (δ : ℂ) • (1 : Mat n) + (t : ℂ) • outerMat v v))
      (star v ⬝ᵥ (psdPow (p - 1) (H + (δ : ℂ) • (1 : Mat n) + (t0 : ℂ) • outerMat v v)).mulVec v).re
      t0 := by
  let Hδ : Mat n := H + (δ : ℂ) • (1 : Mat n)
  let X : Mat n := Hδ + (t0 : ℂ) • outerMat v v
  have hH_t0_psd : (H + (t0 : ℂ) • outerMat v v).PosSemidef := by
    have : (t0 : ℂ) • outerMat v v = t0 • outerMat v v := by ext i j; simp [Complex.real_smul]
    rw [this]; exact hH.add ((outerMat_posSemidef v).smul ht0)
  have hX_psd : X.PosSemidef := by
    have : X = (H + (t0 : ℂ) • outerMat v v) + δ • (1 : Mat n) := by
      ext i j; simp [X, Hδ, Complex.real_smul]; ring
    rw [this]; exact hH_t0_psd.add (Matrix.PosSemidef.one.smul hδ.le)
  let lo : ℝ := δ / 2
  have hlo_pos : 0 < lo := half_pos hδ
  let hi : ℝ := X.trace.re + δ / 2 + 1
  have hX_tr_nn : 0 ≤ X.trace.re := by
    have h1 := re_trace_mul_nonneg_of_posSemidef hX_psd Matrix.PosSemidef.one
    simpa using h1
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  let K : ℝ := (p - 1) * max (lo ^ (p - 2)) (hi ^ (p - 2))
  have hK : ∀ c ∈ Set.Icc lo hi, |(p - 1) * c ^ (p - 2)| ≤ K := by
    intro c hc
    have hc_pos : 0 < c := lt_of_lt_of_le hlo_pos hc.1
    rw [abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hc_pos.le _))]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    by_cases hp2 : 2 ≤ p
    · exact (Real.rpow_le_rpow hc_pos.le hc.2 (by linarith)).trans (le_max_right _ _)
    · have : c ^ (p - 2) ≤ lo ^ (p - 2) := Real.rpow_le_rpow_of_nonpos hlo_pos hc.1 (by linarith)
      exact this.trans (le_max_left _ _)
  -- Prove HasDerivAt via slope bound: for |t - t0| < δ/2, |f(t) - f(t0) - f'(t0)*(t - t0)| ≤ K * (t - t0)^2
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc_pos
  have hK_nn : 0 ≤ K := (abs_nonneg _).trans (hK lo ⟨le_rfl, hlohi⟩)
  let r : ℝ := min (δ / 2) (c / (K + 1))
  have hr_pos : 0 < r := lt_min (half_pos hδ) (div_pos hc_pos (by linarith))
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr_pos] with h hh
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
  have hh_lt_half : |h| < δ / 2 := lt_of_lt_of_le hh (min_le_left _ _)
  have hh_lt_c : |h| < c / (K + 1) := lt_of_lt_of_le hh (min_le_right _ _)
  let Y : Mat n := Hδ + ((t0 + h : ℝ) : ℂ) • outerMat v v
  have hYX : Y - X = (h : ℂ) • outerMat v v := by
    ext i j; simp [Y, X]; ring
  -- Show Y = A + (δ/2) • 1 with A PSD!
  have hY_split : ∃ A : Mat n, A.PosSemidef ∧ Y = A + ((δ / 2 : ℝ) : ℂ) • (1 : Mat n) := by
    -- A := H + t0 • v vᴴ + (δ/2) • 1 + h • v vᴴ; note (δ/2) • 1 + h • v vᴴ ⪰ 0 since |h| < δ/2 and ‖v‖ = 1!
    let B : Mat n := ((δ / 2 : ℝ) : ℂ) • (1 : Mat n) + (h : ℂ) • outerMat v v
    have hB_psd : B.PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      have hHerm : B.IsHermitian := by
        rw [Matrix.IsHermitian]; dsimp [B]
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
          Matrix.conjTranspose_one, (outerMat_posSemidef v).isHermitian.eq]
        simp
      refine ⟨hHerm, fun x => ?_⟩
      rw [Complex.nonneg_iff]
      refine ⟨?_, (isHermitian_im_dotProduct_mulVec_self hHerm x).symm⟩
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_add, dotProduct_smul, dotProduct_smul, Complex.add_re, smul_eq_mul, smul_eq_mul,
        Complex.mul_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re,
        Complex.ofReal_im, outerMat_quad]
      -- Show |(star x ⬝ᵥ v) * (star v ⬝ᵥ x)| = ‖star v ⬝ᵥ x‖^2 ≤ ‖x‖^2 * ‖v‖^2 = (star x ⬝ᵥ x).re
      have hcs : ((star x ⬝ᵥ v) * (star v ⬝ᵥ x)).re ≤ (star x ⬝ᵥ x).re := by
        let xE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
        let vE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
        have hv1 : ‖vE‖ = 1 := by
          have h1 : inner ℂ vE vE = 1 := by
            rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; exact hv
          rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at h1
          have hsq : ‖vE‖ ^ 2 = 1 := (RCLike.ofReal_inj (K := ℂ)).mp (by simpa using h1)
          nlinarith [norm_nonneg vE]
        have hxsq : (star x ⬝ᵥ x).re = ‖xE‖ ^ 2 := by
          have h1 : star x ⬝ᵥ x = inner ℂ xE xE := by
            rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
          rw [h1, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
          change ((‖xE‖ ^ 2 : ℝ) : ℂ).re = ‖xE‖ ^ 2
          exact Complex.ofReal_re _
        have hdot_eq : ((star x ⬝ᵥ v) * (star v ⬝ᵥ x)).re = ‖inner ℂ vE xE‖ ^ 2 := by
          have h1 : star v ⬝ᵥ x = inner ℂ vE xE := by
            rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
          have h2 : star x ⬝ᵥ v = (starRingEnd ℂ) (inner ℂ vE xE) := by
            rw [← h1]; simp only [dotProduct, Pi.star_apply, map_sum, map_mul, Complex.star_def,
              RingHomCompTriple.comp_apply, RingHom.id_apply]
            refine Finset.sum_congr rfl fun i _ => by rw [mul_comm]
          rw [h1, h2, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        rw [hxsq, hdot_eq]
        have := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) vE xE) 2
        simpa [mul_pow, hv1] using this
      have hdot_nn : 0 ≤ ((star x ⬝ᵥ v) * (star v ⬝ᵥ x)).re := by
        have h1 : star x ⬝ᵥ (outerMat v v).mulVec x = (star x ⬝ᵥ v) * (star v ⬝ᵥ x) := outerMat_quad v v x
        rw [← h1]
        simpa [RCLike.re_to_complex] using (outerMat_posSemidef v).re_dotProduct_nonneg x
      have hlow : -|h| ≤ h := neg_abs_le h
      nlinarith
    refine ⟨H + (t0 : ℂ) • outerMat v v + B, hH_t0_psd.add hB_psd, ?_⟩
    ext i j; simp [Y, Hδ, B]; ring
  obtain ⟨AY, hAY_psd, hY_eqA⟩ := hY_split
  have hY_psd : Y.PosSemidef := by
    have : ((δ / 2 : ℝ) : ℂ) • (1 : Mat n) = (δ / 2) • (1 : Mat n) := by ext i j; simp [Complex.real_smul]
    rw [hY_eqA, this]; exact hAY_psd.add (Matrix.PosSemidef.one.smul (half_pos hδ).le)
  have hX_eig : ∀ i, hX_psd.isHermitian.eigenvalues i ∈ Set.Icc lo hi := fun i => by
    have hge : δ ≤ hX_psd.isHermitian.eigenvalues i := by
      have hX_eq : X = (H + (t0 : ℂ) • outerMat v v) + (δ : ℂ) • (1 : Mat n) := by
        ext i j; simp [X, Hδ]; ring
      exact posSemidef_add_smul_one_eigenvalues_ge hH_t0_psd hδ.le (hX_eq ▸ hX_psd) i |> fun h => by
        simpa [hX_eq] using h
    have hle : hX_psd.isHermitian.eigenvalues i ≤ X.trace.re := posSemidef_eigenvalues_le_trace hX_psd i
    exact ⟨by dsimp [lo]; linarith, by dsimp [hi]; linarith⟩
  have hY_eig : ∀ j, hY_psd.isHermitian.eigenvalues j ∈ Set.Icc lo hi := fun j => by
    have hge : lo ≤ hY_psd.isHermitian.eigenvalues j := by
      have := posSemidef_add_smul_one_eigenvalues_ge hAY_psd (half_pos hδ).le (hY_eqA ▸ hY_psd) j
      simpa [hY_eqA] using this
    have hY_tr : Y.trace.re = X.trace.re + h := by
      have : Y = X + (h : ℂ) • outerMat v v := by rw [← hYX]; abel
      rw [this, Matrix.trace_add, Matrix.trace_smul, Complex.add_re, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im]
      have htr1 : (outerMat v v).trace.re = 1 := by
        have := trace_mul_outerMat (1 : Mat n) v
        simp only [Matrix.one_mul, Matrix.one_mulVec] at this
        rw [this, hv, Complex.one_re]
      rw [htr1]; ring
    have hle : hY_psd.isHermitian.eigenvalues j ≤ Y.trace.re := posSemidef_eigenvalues_le_trace hY_psd j
    have hle_abs : h ≤ |h| := le_abs_self h
    exact ⟨hge, by dsimp [hi]; linarith⟩
  have htb := matrix_schattenPow_taylor_bound hp hlo_pos.le hlohi hK (Or.inl hlo_pos) hX_psd hY_psd hX_eig hY_eig
  have htr_lin : (psdPow (p - 1) X * (Y - X)).trace.re =
      h * (star v ⬝ᵥ (psdPow (p - 1) X).mulVec v).re := by
    rw [hYX, Matrix.mul_smul, Matrix.trace_smul, trace_mul_outerMat, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have htr_sq : ((Y - X) * (Y - X)).trace.re = h ^ 2 := by
    rw [hYX, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul]
    have hout_sq : outerMat v v * outerMat v v = outerMat v v := by
      ext i j
      simp only [outerMat, Matrix.mul_apply, Matrix.of_apply]
      have : ∑ k : Fin n, v i * star (v k) * (v k * star (v j)) =
          v i * star (v j) * (star v ⬝ᵥ v) := by
        simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [this, hv, mul_one]
    rw [hout_sq]
    have htr1 : (outerMat v v).trace = 1 := by
      have := trace_mul_outerMat (1 : Mat n) v
      simp only [Matrix.one_mul, Matrix.one_mulVec] at this
      rw [this, hv]
    rw [htr1, smul_eq_mul, mul_one, ← sq, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [htr_lin, htr_sq] at htb
  simp only [Real.norm_eq_abs, smul_eq_mul]
  have heq_goal : (1 / p) * schattenPow p (H + (δ : ℂ) • (1 : Mat n) + ((t0 + h : ℝ) : ℂ) • outerMat v v) -
      (1 / p) * schattenPow p (H + (δ : ℂ) • (1 : Mat n) + (t0 : ℂ) • outerMat v v) -
      h * (star v ⬝ᵥ (psdPow (p - 1) (H + (δ : ℂ) • (1 : Mat n) + (t0 : ℂ) • outerMat v v)).mulVec v).re =
      (1 / p) * schattenPow p Y - (1 / p) * schattenPow p X -
      h * (star v ⬝ᵥ (psdPow (p - 1) X).mulVec v).re := rfl
  rw [heq_goal]
  calc |(1 / p) * schattenPow p Y - (1 / p) * schattenPow p X -
          h * (star v ⬝ᵥ (psdPow (p - 1) X).mulVec v).re|
      ≤ K * h ^ 2 := htb
    _ = K * |h| * |h| := by
        have hsq : h ^ 2 = |h| * |h| := by rw [← sq_abs, sq]
        rw [hsq, ← mul_assoc]
    _ ≤ (K + 1) * (c / (K + 1)) * |h| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg h)
        exact mul_le_mul (by linarith) hh_lt_c.le (abs_nonneg h) (by linarith)
    _ = c * |h| := by rw [mul_div_cancel₀ _ (by linarith)]

/-! ### Löwner Integral Representation & Sherman–Morrison Bound for 0 < q < 1 -/

/-- The positive Löwner normalization constant c_q := ∫_{s ∈ (0, ∞)} s^(q-1) / (s + 1) ds. -/
def lownerConst (q : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), s ^ (q - 1) / (s + 1)

lemma lownerConst_integrable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ (q - 1) / (s + 1)) (Set.Ioi 0) := by
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine MeasureTheory.IntegrableOn.union ?_ ?_
  · -- On (0, 1], bounded by s^(q-1) which is integrable since q - 1 > -1
    have hint : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ (q - 1)) (Set.Ioc 0 1) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := q - 1) (by linarith)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
    refine hint.mono' ?_ ?_
    · exact (measurable_id.pow_const (q - 1) |>.div (measurable_id.add measurable_const)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hs.1.le _) (by linarith [hs.1]))]
      exact div_le_self (Real.rpow_nonneg hs.1.le _) (by linarith [hs.1])
  · -- On (1, ∞), bounded by s^(q-2) which is integrable since q - 2 < -1
    have hint : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ (q - 2)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hint.mono' ?_ ?_
    · exact (measurable_id.pow_const (q - 1) |>.div (measurable_id.add measurable_const)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := zero_lt_one.trans hs
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hs0.le _) (by linarith))]
      have hdiv : s ^ (q - 1) / (s + 1) ≤ s ^ (q - 1) / s :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hs0.le _) hs0 (by linarith)
      refine hdiv.trans (le_of_eq ?_)
      rw [show q - 2 = (q - 1) - 1 by ring, Real.rpow_sub_one hs0.ne' (q - 1)]

lemma lownerConst_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : 0 < lownerConst q := by
  unfold lownerConst
  have hsub : Set.Ioc (1 : ℝ) 2 ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_trans zero_lt_one hs.1
  have hnn : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ s ^ (q - 1) / (s + 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hs
    exact div_nonneg (Real.rpow_nonneg hs0.le _) (by linarith)
  have hmono1 : ∫ s in Set.Ioc (1 : ℝ) 2, s ^ (q - 1) / (s + 1) ≤
      ∫ s in Set.Ioi (0 : ℝ), s ^ (q - 1) / (s + 1) :=
    MeasureTheory.setIntegral_mono_set (lownerConst_integrable hq0 hq1) hnn
      (Filter.Eventually.of_forall hsub)
  have hc_pos : (0 : ℝ) < (2 : ℝ) ^ (q - 1) / 3 :=
    div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)
  have hint_ioc : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ (q - 1) / (s + 1)) (Set.Ioc 1 2) :=
    (lownerConst_integrable hq0 hq1).mono_set hsub
  have hint_c : MeasureTheory.IntegrableOn (fun _ : ℝ => (2 : ℝ) ^ (q - 1) / 3) (Set.Ioc 1 2) :=
    MeasureTheory.integrableOn_const (by simp)
  have hmono2 : ∫ _ in Set.Ioc (1 : ℝ) 2, ((2 : ℝ) ^ (q - 1) / 3) ≤
      ∫ s in Set.Ioc (1 : ℝ) 2, s ^ (q - 1) / (s + 1) := by
    refine MeasureTheory.setIntegral_mono_on hint_c hint_ioc measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 < s := lt_trans zero_lt_one hs.1
    have hnum : (2 : ℝ) ^ (q - 1) ≤ s ^ (q - 1) :=
      Real.rpow_le_rpow_of_nonpos hs0 hs.2 (by linarith)
    have hden : s + 1 ≤ 3 := by linarith [hs.2]
    exact div_le_div₀ (Real.rpow_nonneg hs0.le _) hnum (by linarith) hden
  have hval : ∫ _ in Set.Ioc (1 : ℝ) 2, ((2 : ℝ) ^ (q - 1) / 3) = (2 : ℝ) ^ (q - 1) / 3 := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul]
    have hv : MeasureTheory.volume.real (Set.Ioc (1 : ℝ) 2) = 1 := by
      simp [MeasureTheory.Measure.real, Real.volume_Ioc]
      norm_num
    rw [hv, one_mul]
  linarith

lemma lowner_rpow_integrable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 ≤ x) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ (q - 1) * (x / (x + s))) (Set.Ioi 0) := by
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  have hmeas : Measurable (fun s : ℝ => s ^ (q - 1) * (x / (x + s))) :=
    (measurable_id.pow_const (q - 1)).mul (measurable_const.div (measurable_const.add measurable_id))
  refine MeasureTheory.IntegrableOn.union ?_ ?_
  · have hint : MeasureTheory.IntegrableOn (fun s : ℝ => s ^ (q - 1)) (Set.Ioc 0 1) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := q - 1) (by linarith)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
    refine hint.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    have hxs : 0 < x + s := by linarith [hs.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hs.1.le _) (div_nonneg hx hxs.le))]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hs.1.le _) ((div_le_one hxs).mpr (by linarith [hs.1]))
  · have hint : MeasureTheory.IntegrableOn (fun s : ℝ => x * s ^ (q - 2)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul x
    refine hint.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := zero_lt_one.trans hs
    have hxs : 0 < x + s := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) (div_nonneg hx hxs.le))]
    have hdiv : x / (x + s) ≤ x / s := div_le_div_of_nonneg_left hx hs0 (by linarith)
    calc s ^ (q - 1) * (x / (x + s))
        ≤ s ^ (q - 1) * (x / s) := mul_le_mul_of_nonneg_left hdiv (Real.rpow_nonneg hs0.le _)
      _ = x * (s ^ (q - 1) / s) := by ring
      _ = x * s ^ (q - 2) := by rw [show q - 2 = (q - 1) - 1 by ring, Real.rpow_sub_one hs0.ne' (q - 1)]

lemma lowner_rpow_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 ≤ x) :
    ∫ s in Set.Ioi (0 : ℝ), s ^ (q - 1) * (x / (x + s)) = x ^ q * lownerConst q := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp [Real.zero_rpow hq0.ne']
  · have hsub := MeasureTheory.integral_comp_mul_left_Ioi'
      (g := fun s : ℝ => s ^ (q - 1) * (x / (x + s))) (a := 0) (b := x) hx_pos
    rw [mul_zero] at hsub
    rw [← hsub, smul_eq_mul]
    have hcongr : ∫ u in Set.Ioi (0 : ℝ), (x * u) ^ (q - 1) * (x / (x + x * u)) =
        ∫ u in Set.Ioi (0 : ℝ), x ^ (q - 1) * (u ^ (q - 1) / (u + 1)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      rw [Real.mul_rpow hx_pos.le hu.le]
      have h1 : x / (x + x * u) = 1 / (u + 1) := by
        have hu1 : u + 1 ≠ 0 := by linarith [Set.mem_Ioi.mp hu]
        have hx1 : x + x * u = x * (u + 1) := by ring
        rw [hx1, div_mul_eq_div_div, div_self hx_pos.ne']
      rw [h1]; ring
    rw [hcongr, MeasureTheory.integral_const_mul, ← mul_assoc]
    congr 1
    calc x * x ^ (q - 1) = x ^ (1 : ℝ) * x ^ (q - 1) := by rw [Real.rpow_one]
      _ = x ^ (1 + (q - 1)) := (Real.rpow_add hx_pos 1 (q - 1)).symm
      _ = x ^ q := by ring_nf

/-- Explicit spectral resolvent (M + s I)⁻¹ for a PSD matrix M and s > 0. -/
def psdResolvent {n : ℕ} {M : Mat n} (hM : M.PosSemidef) (s : ℝ) : Mat n :=
  (hM.isHermitian.eigenvectorUnitary : Mat n) *
    Matrix.diagonal (fun i => (((hM.isHermitian.eigenvalues i + s)⁻¹ : ℝ) : ℂ)) *
    (hM.isHermitian.eigenvectorUnitary : Mat n)ᴴ

lemma psdResolvent_posSemidef {n : ℕ} {M : Mat n} (hM : M.PosSemidef) {s : ℝ} (hs : 0 < s) :
    (psdResolvent hM s).PosSemidef := by
  unfold psdResolvent
  have hd : (Matrix.diagonal (fun i => (((hM.isHermitian.eigenvalues i + s)⁻¹ : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro i
    exact_mod_cast inv_nonneg.mpr (by linarith [hM.eigenvalues_nonneg i])
  simpa using hd.mul_mul_conjTranspose_same (hM.isHermitian.eigenvectorUnitary : Mat n)

lemma psdResolvent_mul_add_smul_one {n : ℕ} {M : Mat n} (hM : M.PosSemidef) {s : ℝ} (hs : 0 < s) :
    psdResolvent hM s * (M + (s : ℂ) • (1 : Mat n)) = 1 := by
  let U := hM.isHermitian.eigenvectorUnitary
  let lam := hM.isHermitian.eigenvalues
  have hM_eq : M = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hM.isHermitian.spectral_theorem
  have h1 : (s : ℂ) • (1 : Mat n) = (U : Mat n) * Matrix.diagonal (fun _ => (s : ℂ)) * (U : Mat n)ᴴ := by
    have hd : Matrix.diagonal (fun _ : Fin n => (s : ℂ)) = (s : ℂ) • (1 : Mat n) := by
      ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
    rw [hd, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, unitary_mul_conjTranspose_self U]
  have hMs : M + (s : ℂ) • (1 : Mat n) =
      (U : Mat n) * Matrix.diagonal (fun i => ((lam i + s : ℝ) : ℂ)) * (U : Mat n)ᴴ := by
    rw [hM_eq, h1, ← Matrix.add_mul, ← Matrix.mul_add]
    congr 2; ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [psdResolvent, hMs]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n), unitary_conjTranspose_mul_self U, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  have hdiag1 : Matrix.diagonal (fun i => (((lam i + s)⁻¹ : ℝ) : ℂ) * ((lam i + s : ℝ) : ℂ)) = 1 := by
    ext i j; by_cases hij : i = j
    · subst hij; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (by linarith [hM.eigenvalues_nonneg i]), Complex.ofReal_one]
    · simp [Matrix.diagonal, hij]
  rw [hdiag1, Matrix.one_mul, unitary_mul_conjTranspose_self U]

lemma add_smul_one_mul_psdResolvent {n : ℕ} {M : Mat n} (hM : M.PosSemidef) {s : ℝ} (hs : 0 < s) :
    (M + (s : ℂ) • (1 : Mat n)) * psdResolvent hM s = 1 := by
  have h := congrArg Matrix.conjTranspose (psdResolvent_mul_add_smul_one hM hs)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_one, (psdResolvent_posSemidef hM hs).isHermitian.eq,
    Matrix.conjTranspose_add, hM.isHermitian.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one] at h
  simpa [Complex.conj_ofReal] using h

lemma re_quadForm_psdResolvent_le_inv {n : ℕ} {M : Mat n} (hM : M.PosSemidef) {s : ℝ} (hs : 0 < s)
    (v : Fin n → ℂ) (hv : star v ⬝ᵥ v = 1) :
    (star v ⬝ᵥ (psdResolvent hM s).mulVec v).re ≤ s⁻¹ := by
  let U := hM.isHermitian.eigenvectorUnitary
  let lam := hM.isHermitian.eigenvalues
  let w : Fin n → ℂ := (U : Mat n)ᴴ.mulVec v
  have hw_norm : ∑ i : Fin n, ‖w i‖ ^ 2 = 1 := by
    have h1 : star w ⬝ᵥ w = 1 := by
      have hstar : star w = (star v) ᵥ* (U : Mat n) := by
        simp only [w, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [hstar, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self U,
        Matrix.one_mulVec, hv]
    have hre := congrArg Complex.re h1
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.one_re] at hre
    rw [← hre]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hquad : (star v ⬝ᵥ (psdResolvent hM s).mulVec v).re =
      ∑ i : Fin n, ‖w i‖ ^ 2 * (lam i + s)⁻¹ := by
    have h1 : star v ⬝ᵥ (psdResolvent hM s).mulVec v =
        star w ⬝ᵥ (Matrix.diagonal (fun i => (((lam i + s)⁻¹ : ℝ) : ℂ))).mulVec w := by
      simp only [psdResolvent, Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec]
      have : (star v) ᵥ* (U : Mat n) = star w := by
        simp only [w, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [this]
    rw [h1]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (w i) * ((((lam i + s)⁻¹ : ℝ) : ℂ) * w i) =
        (((lam i + s)⁻¹ : ℝ) : ℂ) * (star (w i) * w i) := by ring
    rw [this, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]; ring
  rw [hquad]
  calc ∑ i : Fin n, ‖w i‖ ^ 2 * (lam i + s)⁻¹
      ≤ ∑ i : Fin n, ‖w i‖ ^ 2 * s⁻¹ := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact inv_anti₀ hs (by linarith [hM.eigenvalues_nonneg i])
    _ = (∑ i : Fin n, ‖w i‖ ^ 2) * s⁻¹ := (Finset.sum_mul ..).symm
    _ = s⁻¹ := by rw [hw_norm, one_mul]

/-- Spectral Löwner integral identity for any PSD matrix M, 0 < q < 1, and any vector v:
    ∫_{s > 0} s^(q-1) * (Re(vᴴ v) - s * Re(vᴴ (M + s I)⁻¹ v)) ds = Re(vᴴ M^q v) * lownerConst q. -/
lemma re_quadForm_psdPow_mul_lownerConst {n : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {M : Mat n} (hM : M.PosSemidef) (v : Fin n → ℂ) :
    (∫ s in Set.Ioi (0 : ℝ),
        s ^ (q - 1) * ((star v ⬝ᵥ v).re - s * (star v ⬝ᵥ (psdResolvent hM s).mulVec v).re)) =
      (star v ⬝ᵥ (psdPow q M).mulVec v).re * lownerConst q := by
  let U := hM.isHermitian.eigenvectorUnitary
  let lam := hM.isHermitian.eigenvalues
  let w : Fin n → ℂ := (U : Mat n)ᴴ.mulVec v
  have hnorm_v : (star v ⬝ᵥ v).re = ∑ i : Fin n, ‖w i‖ ^ 2 := by
    have h1 : star w ⬝ᵥ w = star v ⬝ᵥ v := by
      have hstar : star w = (star v) ᵥ* (U : Mat n) := by
        simp only [w, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [hstar, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self U,
        Matrix.one_mulVec]
    rw [← h1]; simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hres : ∀ s : ℝ, 0 < s →
      (star v ⬝ᵥ (psdResolvent hM s).mulVec v).re = ∑ i : Fin n, ‖w i‖ ^ 2 * (lam i + s)⁻¹ := by
    intro s _
    have h1 : star v ⬝ᵥ (psdResolvent hM s).mulVec v =
        star w ⬝ᵥ (Matrix.diagonal (fun i => (((lam i + s)⁻¹ : ℝ) : ℂ))).mulVec w := by
      simp only [psdResolvent, Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec]
      have : (star v) ᵥ* (U : Mat n) = star w := by
        simp only [w, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [this]
    rw [h1]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (w i) * ((((lam i + s)⁻¹ : ℝ) : ℂ) * w i) =
        (((lam i + s)⁻¹ : ℝ) : ℂ) * (star (w i) * w i) := by ring
    rw [this, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]; ring
  have hpow : (star v ⬝ᵥ (psdPow q M).mulVec v).re = ∑ i : Fin n, ‖w i‖ ^ 2 * (lam i) ^ q := by
    have h1 : star v ⬝ᵥ (psdPow q M).mulVec v =
        star w ⬝ᵥ (Matrix.diagonal (fun i => (((lam i) ^ q : ℝ) : ℂ))).mulVec w := by
      rw [psdPow_eq_spectral hq0 hM]
      simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec]
      have : (star v) ᵥ* (U : Mat n) = star w := by
        simp only [w, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [this]
    rw [h1]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (w i) * ((((lam i) ^ q : ℝ) : ℂ) * w i) =
        (((lam i) ^ q : ℝ) : ℂ) * (star (w i) * w i) := by ring
    rw [this, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]; ring
  have hcongr : ∫ s in Set.Ioi (0 : ℝ),
        s ^ (q - 1) * ((star v ⬝ᵥ v).re - s * (star v ⬝ᵥ (psdResolvent hM s).mulVec v).re) =
      ∫ s in Set.Ioi (0 : ℝ),
        ∑ i : Fin n, ‖w i‖ ^ 2 * (s ^ (q - 1) * (lam i / (lam i + s))) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : 0 < s := hs
    rw [hnorm_v, hres s hs0, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hden : lam i + s ≠ 0 := by linarith [hM.eigenvalues_nonneg i]
    field_simp [hden]; ring
  rw [hcongr, MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul]
    rw [hpow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lowner_rpow_eq hq0 hq1 (hM.eigenvalues_nonneg i), mul_assoc]
  · intro i _
    exact (lowner_rpow_integrable hq0 hq1 (hM.eigenvalues_nonneg i)).const_mul (‖w i‖ ^ 2)

lemma re_quadForm_psdPow_integrable {n : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {M : Mat n} (hM : M.PosSemidef) (v : Fin n → ℂ) :
    MeasureTheory.IntegrableOn
      (fun s : ℝ => s ^ (q - 1) * ((star v ⬝ᵥ v).re - s * (star v ⬝ᵥ (psdResolvent hM s).mulVec v).re))
      (Set.Ioi 0) := by
  let U := hM.isHermitian.eigenvectorUnitary
  let lam := hM.isHermitian.eigenvalues
  let w : Fin n → ℂ := (U : Mat n)ᴴ.mulVec v
  have hint_sum : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∑ i : Fin n, ‖w i‖ ^ 2 * (s ^ (q - 1) * (lam i / (lam i + s)))) (Set.Ioi 0) :=
    MeasureTheory.integrable_finsetSum Finset.univ fun i _ =>
      (lowner_rpow_integrable hq0 hq1 (hM.eigenvalues_nonneg i)).const_mul (‖w i‖ ^ 2)
  refine hint_sum.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs0 : 0 < s := hs
  have hnorm_v : (star v ⬝ᵥ v).re = ∑ i : Fin n, ‖w i‖ ^ 2 := by
    have h1 : star w ⬝ᵥ w = star v ⬝ᵥ v := by
      have hstar : star w = (star v) ᵥ* (U : Mat n) := by
        simp only [w, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [hstar, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self U,
        Matrix.one_mulVec]
    rw [← h1]; simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hres : (star v ⬝ᵥ (psdResolvent hM s).mulVec v).re = ∑ i : Fin n, ‖w i‖ ^ 2 * (lam i + s)⁻¹ := by
    have h1 : star v ⬝ᵥ (psdResolvent hM s).mulVec v =
        star w ⬝ᵥ (Matrix.diagonal (fun i => (((lam i + s)⁻¹ : ℝ) : ℂ))).mulVec w := by
      simp only [psdResolvent, Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec]
      have : (star v) ᵥ* (U : Mat n) = star w := by
        simp only [w, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [this]
    rw [h1]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (w i) * ((((lam i + s)⁻¹ : ℝ) : ℂ) * w i) =
        (((lam i + s)⁻¹ : ℝ) : ℂ) * (star (w i) * w i) := by ring
    rw [this, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]; ring
  rw [hnorm_v, hres, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hden : lam i + s ≠ 0 := by linarith [hM.eigenvalues_nonneg i]
  field_simp [hden]; ring

/-- Löwner–Heinz Operator Monotonicity (0 < q < 1): 0 ⪯ X ⪯ Y implies X^q ⪯ Y^q! -/
theorem psdPow_mono_of_posSemidef {n : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {X Y : Mat n} (hX : X.PosSemidef) (hY : Y.PosSemidef) (hYX : (Y - X).PosSemidef) :
    (psdPow q Y - psdPow q X).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hHerm : (psdPow q Y - psdPow q X).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, (psdPow_posSemidef hq0 hY).isHermitian.eq,
      (psdPow_posSemidef hq0 hX).isHermitian.eq]
  refine ⟨hHerm, fun v => ?_⟩
  rw [Complex.nonneg_iff]
  refine ⟨?_, (isHermitian_im_dotProduct_mulVec_self hHerm v).symm⟩
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg]
  have hcq := lownerConst_pos hq0 hq1
  suffices h : (star v ⬝ᵥ (psdPow q X).mulVec v).re * lownerConst q ≤
      (star v ⬝ᵥ (psdPow q Y).mulVec v).re * lownerConst q by nlinarith
  rw [← re_quadForm_psdPow_mul_lownerConst hq0 hq1 hX v,
    ← re_quadForm_psdPow_mul_lownerConst hq0 hq1 hY v]
  refine MeasureTheory.setIntegral_mono_on
    (re_quadForm_psdPow_integrable hq0 hq1 hX v)
    (re_quadForm_psdPow_integrable hq0 hq1 hY v) measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hs0.le _)
  -- Operator anti-monotonicity of resolvent: Re(vᴴ R_Y v) ≤ Re(vᴴ R_X v)
  have hanti : (star v ⬝ᵥ (psdResolvent hY s).mulVec v).re ≤
      (star v ⬝ᵥ (psdResolvent hX s).mulVec v).re := by
    let y : Fin n → ℂ := (psdResolvent hY s).mulVec v
    let z : Fin n → ℂ := (psdResolvent hX s).mulVec v
    have hXs_psd : (X + (s : ℂ) • (1 : Mat n)).PosSemidef := by
      have : (s : ℂ) • (1 : Mat n) = s • (1 : Mat n) := by ext i j; simp [Complex.real_smul]
      rw [this]; exact hX.add (Matrix.PosSemidef.one.smul hs0.le)
    have hdiff_nn : 0 ≤ (star (y - z) ⬝ᵥ (X + (s : ℂ) • (1 : Mat n)).mulVec (y - z)).re := by
      simpa [RCLike.re_to_complex] using hXs_psd.re_dotProduct_nonneg (y - z)
    have hXs_z : (X + (s : ℂ) • (1 : Mat n)).mulVec z = v := by
      simp only [z, Matrix.mulVec_mulVec, add_smul_one_mul_psdResolvent hX hs0, Matrix.one_mulVec]
    have hYs_y : (Y + (s : ℂ) • (1 : Mat n)).mulVec y = v := by
      simp only [y, Matrix.mulVec_mulVec, add_smul_one_mul_psdResolvent hY hs0, Matrix.one_mulVec]
    have hzy : (star z ⬝ᵥ (X + (s : ℂ) • (1 : Mat n)).mulVec y).re = (star v ⬝ᵥ y).re := by
      have h1 : star z ⬝ᵥ (X + (s : ℂ) • (1 : Mat n)).mulVec y =
          star ((X + (s : ℂ) • (1 : Mat n)).mulVec z) ⬝ᵥ y := by
        conv_rhs => rw [Matrix.star_mulVec, hXs_psd.isHermitian.eq, ← Matrix.dotProduct_mulVec]
      rw [h1, hXs_z]
    have hvy_sym : (star y ⬝ᵥ v).re = (star v ⬝ᵥ y).re := by
      have h1 : star (star y ⬝ᵥ v) = star v ⬝ᵥ y := by
        simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
        refine Finset.sum_congr rfl fun i _ => by rw [mul_comm]
      rw [← h1, Complex.star_def, Complex.conj_re]
    have hexp : (star (y - z) ⬝ᵥ (X + (s : ℂ) • (1 : Mat n)).mulVec (y - z)).re =
        (star y ⬝ᵥ (X + (s : ℂ) • (1 : Mat n)).mulVec y).re - 2 * (star v ⬝ᵥ y).re + (star v ⬝ᵥ z).re := by
      have hzv_sym : (star z ⬝ᵥ v).re = (star v ⬝ᵥ z).re := by
        have h1 : star (star z ⬝ᵥ v) = star v ⬝ᵥ z := by
          simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
          refine Finset.sum_congr rfl fun i _ => by rw [mul_comm]
        rw [← h1, Complex.star_def, Complex.conj_re]
      rw [Matrix.mulVec_sub, hXs_z, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
        Complex.sub_re, Complex.sub_re, Complex.sub_re, hzy, hvy_sym, hzv_sym]; ring
    have hYX_y : (star y ⬝ᵥ (X + (s : ℂ) • (1 : Mat n)).mulVec y).re ≤ (star v ⬝ᵥ y).re := by
      have h1 : (star y ⬝ᵥ (Y - X).mulVec y).re ≥ 0 := by
        simpa [RCLike.re_to_complex] using hYX.re_dotProduct_nonneg y
      have h2 : (Y + (s : ℂ) • (1 : Mat n)) - (X + (s : ℂ) • (1 : Mat n)) = Y - X := by abel
      have h3 : (star y ⬝ᵥ (Y + (s : ℂ) • (1 : Mat n)).mulVec y).re -
          (star y ⬝ᵥ (X + (s : ℂ) • (1 : Mat n)).mulVec y).re = (star y ⬝ᵥ (Y - X).mulVec y).re := by
        rw [← h2, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
      rw [hYs_y, hvy_sym] at h3
      linarith
    linarith
  nlinarith

/-- Exact Sherman–Morrison rank-1 bound for 0 < q < 1:
    Re(vᴴ (A + t v vᴴ)^q v) ≤ Re(vᴴ A^q v) + t^q for all PSD A, unit v, t ≥ 0. -/
theorem re_quadForm_psdPow_add_rankOne_le {n : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {A : Mat n} (hA : A.PosSemidef) (v : Fin n → ℂ) (hv : star v ⬝ᵥ v = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (star v ⬝ᵥ (psdPow q (A + (t : ℂ) • outerMat v v)).mulVec v).re ≤
      (star v ⬝ᵥ (psdPow q A).mulVec v).re + t ^ q := by
  let M : Mat n := A + (t : ℂ) • outerMat v v
  have hM : M.PosSemidef := by
    have : (t : ℂ) • outerMat v v = t • outerMat v v := by ext i j; simp [Complex.real_smul]
    rw [show M = A + t • outerMat v v by rw [← this]]
    exact hA.add ((outerMat_posSemidef v).smul ht)
  have hcq := lownerConst_pos hq0 hq1
  suffices h : (star v ⬝ᵥ (psdPow q M).mulVec v).re * lownerConst q ≤
      (star v ⬝ᵥ (psdPow q A).mulVec v).re * lownerConst q + t ^ q * lownerConst q by nlinarith
  rw [← re_quadForm_psdPow_mul_lownerConst hq0 hq1 hM v,
    ← re_quadForm_psdPow_mul_lownerConst hq0 hq1 hA v,
    ← lowner_rpow_eq hq0 hq1 ht]
  rw [← MeasureTheory.integral_add (re_quadForm_psdPow_integrable hq0 hq1 hA v)
    (lowner_rpow_integrable hq0 hq1 ht)]
  refine MeasureTheory.setIntegral_mono_on
    (re_quadForm_psdPow_integrable hq0 hq1 hM v)
    ((re_quadForm_psdPow_integrable hq0 hq1 hA v).add (lowner_rpow_integrable hq0 hq1 ht))
    measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  let RA := psdResolvent hA s
  let RM := psdResolvent hM s
  let w : Fin n → ℂ := RA.mulVec v
  let α : ℝ := (star v ⬝ᵥ w).re
  have hα_nn : 0 ≤ α := by
    simpa [RCLike.re_to_complex, α, w] using (psdResolvent_posSemidef hA hs0).re_dotProduct_nonneg v
  have hα_le : α ≤ s⁻¹ := re_quadForm_psdResolvent_le_inv hA hs0 v hv
  have hα_complex : star v ⬝ᵥ w = (α : ℂ) := by
    apply Complex.ext
    · rfl
    · change (star v ⬝ᵥ (psdResolvent hA s).mulVec v).im = 0
      exact isHermitian_im_dotProduct_mulVec_self (psdResolvent_posSemidef hA hs0).isHermitian v
  -- Sherman–Morrison rank-1 vector identity: (M + s I) w = (1 + t α) v
  have hSM : (M + (s : ℂ) • (1 : Mat n)).mulVec w = ((1 + t * α : ℝ) : ℂ) • v := by
    have hsplit : M + (s : ℂ) • (1 : Mat n) = (A + (s : ℂ) • (1 : Mat n)) + (t : ℂ) • outerMat v v := by
      dsimp [M]; abel
    rw [hsplit, Matrix.add_mulVec, Matrix.smul_mulVec]
    have h1 : (A + (s : ℂ) • (1 : Mat n)).mulVec w = v := by
      simp only [w, RA, Matrix.mulVec_mulVec, add_smul_one_mul_psdResolvent hA hs0, Matrix.one_mulVec]
    have h2 : (outerMat v v).mulVec w = (α : ℂ) • v := by
      ext i
      simp only [outerMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      have : ∑ j : Fin n, v i * star (v j) * w j = v i * (star v ⬝ᵥ w) := by
        simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [this, hα_complex]; ring
    rw [h1, h2, smul_smul]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_one]; ring
  have hRM_eq : (star v ⬝ᵥ RM.mulVec v).re = α / (1 + t * α) := by
    have h1 := congrArg (Matrix.mulVec RM) hSM
    rw [Matrix.mulVec_mulVec, psdResolvent_mul_add_smul_one hM hs0, Matrix.one_mulVec,
      Matrix.mulVec_smul] at h1
    have h2 := congrArg (fun x => (star v ⬝ᵥ x).re) h1
    rw [dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at h2
    have hden : 0 < 1 + t * α := by nlinarith
    rw [eq_div_iff hden.ne']; linarith
  have hv_re : (star v ⬝ᵥ v).re = 1 := by rw [hv, Complex.one_re]
  -- Pointwise algebraic inequality: 1 - s * α / (1 + t α) ≤ (1 - s α) + t / (t + s)
  have hpt : (1 - s * (α / (1 + t * α))) ≤ (1 - s * α) + t / (t + s) := by
    have h1ta : 0 < 1 + t * α := by nlinarith
    have hts : 0 < t + s := by linarith
    have hsa : s * α ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hα_le hs0.le
      rwa [mul_inv_cancel₀ hs0.ne'] at this
    rw [sub_le_iff_le_add]
    have hdiff : (1 - s * (α / (1 + t * α))) - (1 - s * α) = s * t * α ^ 2 / (1 + t * α) := by
      field_simp [h1ta.ne']; ring
    have hle : s * t * α ^ 2 / (1 + t * α) ≤ t / (t + s) := by
      rw [div_le_div_iff₀ h1ta hts]
      have h1 : s * t * α ^ 2 * (t + s) = t ^ 2 * (s * α) * α + t * (s * α) ^ 2 := by ring
      have h2 : t * (1 + t * α) = t ^ 2 * α + t := by ring
      rw [h1, h2]
      have hsq : (s * α) ^ 2 ≤ 1 := by nlinarith [mul_nonneg hs0.le hα_nn]
      have hterm1 : t ^ 2 * (s * α) * α ≤ t ^ 2 * α := by
        have := mul_le_mul_of_nonneg_right hsa (mul_nonneg (sq_nonneg t) hα_nn)
        nlinarith
      nlinarith [hterm1]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hpt (Real.rpow_nonneg hs0.le (q - 1))
  rw [mul_add] at hmul
  rw [hv_re, hRM_eq]
  exact hmul

/-! ### Lemma 4(a): Sharp Rank-One Smoothness for 1 < p < 2 -/

/-- Lemma 4(a): For 1 < p < 2, any PSD matrix H, any unit vector v, and any ε ≥ 0,
    (1/p) ‖H + ε v vᴴ‖_p^p ≤ (1/p) ‖H‖_p^p + ε Re(vᴴ H^(p-1) v) + (1/p) ε^p. -/
theorem lemma4a_rank_one_smoothness {n : ℕ} {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    {H : Mat n} (hH : H.PosSemidef) (v : Fin n → ℂ) (hv : star v ⬝ᵥ v = 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (1 / p) * schattenPow p (H + (ε : ℂ) • outerMat v v) ≤
      (1 / p) * schattenPow p H + ε * (star v ⬝ᵥ (psdPow (p - 1) H).mulVec v).re +
        (1 / p) * ε ^ p := by
  have hp0 : 0 < p := by linarith
  have hpm1 : 0 < p - 1 := by linarith
  have hpm1_lt1 : p - 1 < 1 := by linarith
  -- Step 1: Prove the inequality for H + δ I for every δ > 0 via monotoneOn_of_deriv_nonneg
  have hdelta : ∀ δ : ℝ, 0 < δ →
      (1 / p) * schattenPow p (H + (δ : ℂ) • (1 : Mat n) + (ε : ℂ) • outerMat v v) ≤
        (1 / p) * schattenPow p (H + (δ : ℂ) • (1 : Mat n)) +
          ε * (star v ⬝ᵥ (psdPow (p - 1) (H + (δ : ℂ) • (1 : Mat n))).mulVec v).re +
          (1 / p) * ε ^ p := by
    intro δ hδ
    let Hδ : Mat n := H + (δ : ℂ) • (1 : Mat n)
    have hHδ : Hδ.PosSemidef := by
      have : (δ : ℂ) • (1 : Mat n) = δ • (1 : Mat n) := by ext i j; simp [Complex.real_smul]
      rw [show Hδ = H + δ • (1 : Mat n) by rw [← this]]
      exact hH.add (Matrix.PosSemidef.one.smul hδ.le)
    let c0 : ℝ := (star v ⬝ᵥ (psdPow (p - 1) Hδ).mulVec v).re
    let φ : ℝ → ℝ := fun t =>
      (1 / p) * schattenPow p Hδ + t * c0 + (1 / p) * t ^ p -
        (1 / p) * schattenPow p (Hδ + (t : ℂ) • outerMat v v)
    have hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
        HasDerivAt φ (c0 + t ^ (p - 1) -
          (star v ⬝ᵥ (psdPow (p - 1) (Hδ + (t : ℂ) • outerMat v v)).mulVec v).re) t := by
      intro t ht
      have h1 : HasDerivAt (fun x : ℝ => (1 / p) * schattenPow p Hδ + x * c0) c0 t := by
        simpa using (hasDerivAt_id t |>.mul_const c0).const_add ((1 / p) * schattenPow p Hδ)
      have h2 : HasDerivAt (fun x : ℝ => (1 / p) * x ^ p) (t ^ (p - 1)) t := by
        have hrp := Real.hasDerivAt_rpow_const (p := p) (x := t) (Or.inr hp1.le)
        have hm := hrp.const_mul (1 / p)
        have hsimp : (1 / p) * (p * t ^ (p - 1)) = t ^ (p - 1) := by field_simp [hp0.ne']
        rwa [hsimp] at hm
      have h3 := hasDerivAt_schattenPow_psd_add_rankOne hp1 hδ hH v hv ht
      exact (h1.add h2).sub h3
    have hcont : ContinuousOn φ (Set.Ici 0) :=
      fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ φ (interior (Set.Ici (0 : ℝ))) := fun t ht =>
      (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    have hnn : ∀ t ∈ interior (Set.Ici (0 : ℝ)), 0 ≤ deriv φ t := by
      intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      rw [(hderiv t ht0).deriv]
      have hsm := re_quadForm_psdPow_add_rankOne_le hpm1 hpm1_lt1 hHδ v hv ht0
      linarith
    have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff hnn
    have h0le := hmono (Set.self_mem_Ici) hε hε
    have hφ0 : φ 0 = 0 := by simp [φ, Real.zero_rpow hp0.ne']
    rw [hφ0] at h0le
    have hgoal : 0 ≤ (1 / p) * schattenPow p (H + (δ : ℂ) • (1 : Mat n)) +
        ε * (star v ⬝ᵥ (psdPow (p - 1) (H + (δ : ℂ) • (1 : Mat n))).mulVec v).re +
        (1 / p) * ε ^ p -
        (1 / p) * schattenPow p (H + (δ : ℂ) • (1 : Mat n) + (ε : ℂ) • outerMat v v) := h0le
    linarith
  -- Step 2: Send δ → 0⁺!
  have hcont_pow : Continuous (fun M : Mat n => schattenPow p M) := by
    have heq : (fun M : Mat n => schattenPow p M) = fun M => (schattenNorm p M) ^ p := by
      ext M; exact (schattenNorm_rpow hp0 M).symm
    rw [heq]
    exact (Real.continuous_rpow_const hp0.le).comp (continuous_schattenNorm hp1)
  have hL_tend : Filter.Tendsto
      (fun δ : ℝ => (1 / p) * schattenPow p (H + (δ : ℂ) • (1 : Mat n) + (ε : ℂ) • outerMat v v))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / p) * schattenPow p (H + (ε : ℂ) • outerMat v v))) := by
    have hmat : Continuous (fun δ : ℝ => H + (δ : ℂ) • (1 : Mat n) + (ε : ℂ) • outerMat v v) :=
      (continuous_const.add ((Complex.continuous_ofReal.smul continuous_const))).add continuous_const
    have h1 : Filter.Tendsto
        (fun δ : ℝ => (1 / p) * schattenPow p (H + (δ : ℂ) • (1 : Mat n) + (ε : ℂ) • outerMat v v))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((1 / p) * schattenPow p (H + ((0 : ℝ) : ℂ) • (1 : Mat n) + (ε : ℂ) • outerMat v v))) :=
      ((continuous_const.mul (hcont_pow.comp hmat)).tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h1
  have hR1_tend : Filter.Tendsto
      (fun δ : ℝ => (1 / p) * schattenPow p (H + (δ : ℂ) • (1 : Mat n)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / p) * schattenPow p H)) := by
    have hmat : Continuous (fun δ : ℝ => H + (δ : ℂ) • (1 : Mat n)) :=
      continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
    have h1 : Filter.Tendsto
        (fun δ : ℝ => (1 / p) * schattenPow p (H + (δ : ℂ) • (1 : Mat n)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((1 / p) * schattenPow p (H + ((0 : ℝ) : ℂ) • (1 : Mat n)))) :=
      ((continuous_const.mul (hcont_pow.comp hmat)).tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h1
  have hR2_tend : Filter.Tendsto
      (fun δ : ℝ => (star v ⬝ᵥ (psdPow (p - 1) (H + (δ : ℂ) • (1 : Mat n))).mulVec v).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((star v ⬝ᵥ (psdPow (p - 1) H).mulVec v).re)) := by
    let U := hH.isHermitian.eigenvectorUnitary
    let lam := hH.isHermitian.eigenvalues
    let w : Fin n → ℂ := (U : Mat n)ᴴ.mulVec v
    have hformula : ∀ δ : ℝ, 0 ≤ δ →
        (star v ⬝ᵥ (psdPow (p - 1) (H + (δ : ℂ) • (1 : Mat n))).mulVec v).re =
          ∑ i : Fin n, ‖w i‖ ^ 2 * (lam i + δ) ^ (p - 1) := by
      intro δ hδ
      rw [psdPow_add_smul_one hpm1 hH δ hδ]
      have h1 : star v ⬝ᵥ ((U : Mat n) * Matrix.diagonal (fun i => (((lam i + δ) ^ (p - 1) : ℝ) : ℂ)) *
            (U : Mat n)ᴴ).mulVec v =
          star w ⬝ᵥ (Matrix.diagonal (fun i => (((lam i + δ) ^ (p - 1) : ℝ) : ℂ))).mulVec w := by
        simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
        rw [Matrix.dotProduct_mulVec]
        have : (star v) ᵥ* (U : Mat n) = star w := by
          simp only [w, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
        rw [this]
      rw [h1]
      simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : star (w i) * ((((lam i + δ) ^ (p - 1) : ℝ) : ℂ) * w i) =
          (((lam i + δ) ^ (p - 1) : ℝ) : ℂ) * (star (w i) * w i) := by ring
      rw [this, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        Complex.ofReal_re]; ring
    have h0 := hformula 0 le_rfl
    simp only [Complex.ofReal_zero, zero_smul, add_zero] at h0
    rw [h0]
    have hcont_sum : Continuous (fun δ : ℝ => ∑ i : Fin n, ‖w i‖ ^ 2 * (lam i + δ) ^ (p - 1)) :=
      continuous_finsetSum Finset.univ fun i _ =>
        continuous_const.mul ((Real.continuous_rpow_const hpm1.le).comp (continuous_const.add continuous_id))
    have htend0 : Filter.Tendsto (fun δ : ℝ => ∑ i : Fin n, ‖w i‖ ^ 2 * (lam i + δ) ^ (p - 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∑ i : Fin n, ‖w i‖ ^ 2 * (lam i + 0) ^ (p - 1))) :=
      (hcont_sum.tendsto 0).mono_left nhdsWithin_le_nhds
    simp only [add_zero] at htend0
    refine htend0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hformula δ (Set.mem_Ioi.mp hδ).le).symm
  have hR_tend : Filter.Tendsto
      (fun δ : ℝ => (1 / p) * schattenPow p (H + (δ : ℂ) • (1 : Mat n)) +
          ε * (star v ⬝ᵥ (psdPow (p - 1) (H + (δ : ℂ) • (1 : Mat n))).mulVec v).re +
          (1 / p) * ε ^ p)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / p) * schattenPow p H + ε * (star v ⬝ᵥ (psdPow (p - 1) H).mulVec v).re +
          (1 / p) * ε ^ p)) :=
    ((hR1_tend.add (hR2_tend.const_mul ε)).add tendsto_const_nhds)
  exact le_of_tendsto_of_tendsto hL_tend hR_tend
    (by filter_upwards [self_mem_nhdsWithin] with δ hδ; exact hdelta δ hδ)

/-! ### Helper Bridges for Lemma 4(b), Proposition 5, and Theorem 1 -/

/-- Independence of dualOp from SVD choice: if S = U diag(σ) Vᴴ with σ ≥ 0 and p > 1,
    then dualOp p S = U diag(σ^(p-1)) Vᴴ. -/
lemma dualOp_eq_of_svd {n : ℕ} {p : ℝ} (hp : 1 < p) {S : Mat n}
    (U V : Matrix.unitaryGroup (Fin n) ℂ) (σ : Fin n → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (hS : S = (U : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ) :
    dualOp p S = (U : Mat n) * Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * (V : Mat n)ᴴ := by
  have hpm1 : 0 < p - 1 := by linarith
  obtain ⟨U0, V0, σ0, hσ0, hS0, hG0, _⟩ := exists_svd_dualOp p S
  rw [hG0]
  let P : Mat n := (U : Mat n)ᴴ * (U0 : Mat n)
  let Q : Mat n := (V : Mat n)ᴴ * (V0 : Mat n)
  have hPS : P * Matrix.diagonal (fun i => (σ0 i : ℂ)) = Matrix.diagonal (fun i => (σ i : ℂ)) * Q := by
    have h1 : (U : Mat n)ᴴ * S * (V0 : Mat n) = (U : Mat n)ᴴ * S * (V0 : Mat n) := rfl
    conv_lhs at h1 => rw [hS0]
    conv_rhs at h1 => rw [hS]
    simp only [Matrix.mul_assoc] at h1
    rw [unitary_conjTranspose_mul_self V0, Matrix.mul_one,
      ← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n), unitary_conjTranspose_mul_self U, Matrix.one_mul] at h1
    simpa [P, Q, Matrix.mul_assoc] using h1
  have hP2 : P * Matrix.diagonal (fun i => (((σ0 i ^ 2 : ℝ) : ℂ))) =
      Matrix.diagonal (fun i => (((σ i ^ 2 : ℝ) : ℂ))) * P := by
    have hSS : S * Sᴴ = S * Sᴴ := rfl
    have hSS0 : S * Sᴴ = (U0 : Mat n) * Matrix.diagonal (fun i => (((σ0 i ^ 2 : ℝ) : ℂ))) * (U0 : Mat n)ᴴ := by
      conv_lhs => rw [hS0]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.diagonal_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (V0 : Mat n)ᴴ (V0 : Mat n), unitary_conjTranspose_mul_self V0, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp [Complex.conj_ofReal, sq]
      · simp [Matrix.diagonal, hij]
    have hSS1 : S * Sᴴ = (U : Mat n) * Matrix.diagonal (fun i => (((σ i ^ 2 : ℝ) : ℂ))) * (U : Mat n)ᴴ := by
      conv_lhs => rw [hS]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.diagonal_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (V : Mat n)ᴴ (V : Mat n), unitary_conjTranspose_mul_self V, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp [Complex.conj_ofReal, sq]
      · simp [Matrix.diagonal, hij]
    have h2 : (U : Mat n)ᴴ * (S * Sᴴ) * (U0 : Mat n) = (U : Mat n)ᴴ * (S * Sᴴ) * (U0 : Mat n) := rfl
    conv_lhs at h2 => rw [hSS0]
    conv_rhs at h2 => rw [hSS1]
    simp only [Matrix.mul_assoc] at h2
    rw [unitary_conjTranspose_mul_self U0, Matrix.mul_one,
      ← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n), unitary_conjTranspose_mul_self U, Matrix.one_mul] at h2
    simpa [P, Matrix.mul_assoc] using h2
  have hQ2 : Q * Matrix.diagonal (fun i => (((σ0 i ^ 2 : ℝ) : ℂ))) =
      Matrix.diagonal (fun i => (((σ i ^ 2 : ℝ) : ℂ))) * Q := by
    have hSS0 : Sᴴ * S = (V0 : Mat n) * Matrix.diagonal (fun i => (((σ0 i ^ 2 : ℝ) : ℂ))) * (V0 : Mat n)ᴴ := by
      conv_lhs => rw [hS0]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.diagonal_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U0 : Mat n)ᴴ (U0 : Mat n), unitary_conjTranspose_mul_self U0, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp [Complex.conj_ofReal, sq]
      · simp [Matrix.diagonal, hij]
    have hSS1 : Sᴴ * S = (V : Mat n) * Matrix.diagonal (fun i => (((σ i ^ 2 : ℝ) : ℂ))) * (V : Mat n)ᴴ := by
      conv_lhs => rw [hS]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.diagonal_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n), unitary_conjTranspose_mul_self U, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp [Complex.conj_ofReal, sq]
      · simp [Matrix.diagonal, hij]
    have h2 : (V : Mat n)ᴴ * (Sᴴ * S) * (V0 : Mat n) = (V : Mat n)ᴴ * (Sᴴ * S) * (V0 : Mat n) := rfl
    conv_lhs at h2 => rw [hSS0]
    conv_rhs at h2 => rw [hSS1]
    simp only [Matrix.mul_assoc] at h2
    rw [unitary_conjTranspose_mul_self V0, Matrix.mul_one,
      ← Matrix.mul_assoc (V : Mat n)ᴴ (V : Mat n), unitary_conjTranspose_mul_self V, Matrix.one_mul] at h2
    simpa [Q, Matrix.mul_assoc] using h2
  have hPG : P * Matrix.diagonal (fun i => (((σ0 i) ^ (p - 1) : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * Q := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hPS_ij := congr_fun (congr_fun hPS i) j
    have hP2_ij := congr_fun (congr_fun hP2 i) j
    have hQ2_ij := congr_fun (congr_fun hQ2 i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hPS_ij hP2_ij hQ2_ij
    by_cases hσeq : σ i = σ0 j
    · rw [hσeq]
      by_cases h0 : σ0 j = 0
      · simp [h0, Real.zero_rpow hpm1.ne']
      · have hPQ : P i j = Q i j := by
          rw [hσeq] at hPS_ij
          have hne : (σ0 j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
          exact mul_right_cancel₀ hne (by rw [hPS_ij, mul_comm])
        rw [hPQ, mul_comm]
    · have hsq_ne : (σ0 j ^ 2 : ℂ) - (σ i ^ 2 : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]
        intro heq
        have h1 : (σ0 j - σ i) * (σ0 j + σ i) = 0 := by linarith
        rcases mul_eq_zero.mp h1 with h2 | h2
        · exact hσeq (by linarith)
        · have : σ0 j = 0 ∧ σ i = 0 := by constructor <;> linarith [hσ i, hσ0 j]
          exact hσeq (by linarith [this.1, this.2])
      have hP0 : P i j = 0 := by
        have : P i j * ((σ0 j ^ 2 : ℂ) - (σ i ^ 2 : ℂ)) = 0 := by
          have h1 : P i j * (((σ0 j ^ 2 : ℝ) : ℂ)) = (((σ i ^ 2 : ℝ) : ℂ)) * P i j := hP2_ij
          push_cast at h1; linear_combination h1
        exact (mul_eq_zero.mp this).resolve_right hsq_ne
      have hQ0 : Q i j = 0 := by
        have : Q i j * ((σ0 j ^ 2 : ℂ) - (σ i ^ 2 : ℂ)) = 0 := by
          have h1 : Q i j * (((σ0 j ^ 2 : ℝ) : ℂ)) = (((σ i ^ 2 : ℝ) : ℂ)) * Q i j := hQ2_ij
          push_cast at h1; linear_combination h1
        exact (mul_eq_zero.mp this).resolve_right hsq_ne
      simp [hP0, hQ0]
  calc (U0 : Mat n) * Matrix.diagonal (fun i => (((σ0 i) ^ (p - 1) : ℝ) : ℂ)) * (V0 : Mat n)ᴴ
      = (U : Mat n) * (P * Matrix.diagonal (fun i => (((σ0 i) ^ (p - 1) : ℝ) : ℂ))) * (V0 : Mat n)ᴴ := by
        simp only [P, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (U : Mat n) (U : Mat n)ᴴ, unitary_mul_conjTranspose_self U, Matrix.one_mul]
    _ = (U : Mat n) * (Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * Q) * (V0 : Mat n)ᴴ := by
        rw [hPG]
    _ = (U : Mat n) * Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * (V : Mat n)ᴴ := by
        simp only [Q, Matrix.mul_assoc]
        rw [unitary_mul_conjTranspose_self V0, Matrix.mul_one]

lemma dualOp_padZero {n : ℕ} {p : ℝ} (hp : 1 < p) (S : Mat n) :
    dualOp p (padZero S) = padZero (dualOp p S) := by
  have hpm1 : 0 < p - 1 := by linarith
  obtain ⟨U, V, σ, hσ, hS, hG, _⟩ := exists_svd_dualOp p S
  let σExt : Fin (n + 1) → ℝ := fun i => if hi : i.val < n then σ ⟨i.val, hi⟩ else 0
  have hσExt : ∀ i, 0 ≤ σExt i := fun i => by dsimp [σExt]; split_ifs; exact hσ _; exact le_rfl
  have hDiag : padZero (Matrix.diagonal (fun i => (σ i : ℂ))) =
      Matrix.diagonal (fun i => (σExt i : ℂ)) := by
    rw [padZero_diagonal]; congr 1; ext i; dsimp [σExt]; split_ifs <;> simp
  have hpadS : padZero S = (padUnitary U : Mat (n + 1)) *
      Matrix.diagonal (fun i => (σExt i : ℂ)) * (padUnitary V : Mat (n + 1))ᴴ := by
    rw [hS, ← padZero_mul_padUnitary_conjTranspose, ← padUnitary_mul_padZero, hDiag]
  rw [dualOp_eq_of_svd hp (padUnitary U) (padUnitary V) σExt hσExt hpadS, hG,
    ← padZero_mul_padUnitary_conjTranspose, ← padUnitary_mul_padZero, padZero_diagonal]
  congr 2; congr 1; ext i; dsimp [σExt]
  by_cases hi : i.val < n
  · simp [hi]
  · simp [hi, Real.zero_rpow hpm1.ne']

/-- Kernel equality: ker((dualOp p S)ᴴ) = ker(Sᴴ) for all p > 1. -/
lemma ker_dualOp_conjTranspose_eq {n : ℕ} {p : ℝ} (hp : 1 < p) (S : Mat n) :
    LinearMap.ker (Matrix.mulVecLin (dualOp p S)ᴴ) = LinearMap.ker (Matrix.mulVecLin Sᴴ) := by
  have hpm1 : 0 < p - 1 := by linarith
  obtain ⟨U, V, σ, hσ, hS, hG, _⟩ := exists_svd_dualOp p S
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hSH : Sᴴ = (V : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (U : Mat n)ᴴ := by
    rw [hS, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    congr 2; ext i j; by_cases hij : i = j
    · subst hij; simp [Complex.conj_ofReal]
    · simp [Matrix.diagonal, hij]
  have hGH : (dualOp p S)ᴴ =
      (V : Mat n) * Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * (U : Mat n)ᴴ := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    congr 2; ext i j; by_cases hij : i = j
    · subst hij; simp [Complex.conj_ofReal]
    · simp [Matrix.diagonal, hij]
  let y : Fin n → ℂ := (U : Mat n)ᴴ.mulVec x
  have hiff : ∀ d : Fin n → ℝ,
      ((V : Mat n) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Mat n)ᴴ).mulVec x = 0 ↔
        ∀ i, (d i : ℂ) * y i = 0 := by
    intro d
    constructor
    · intro h0
      have h1 := congrArg (Matrix.mulVec (V : Mat n)ᴴ) h0
      simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
      rw [← Matrix.mul_assoc (V : Mat n)ᴴ (V : Mat n), unitary_conjTranspose_mul_self V,
        Matrix.one_mul, ← Matrix.mulVec_mulVec] at h1
      intro i
      simpa [y, Matrix.mulVec_diagonal] using congr_fun h1 i
    · intro hi
      simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
      change (V : Mat n).mulVec ((Matrix.diagonal (fun i => (d i : ℂ))).mulVec y) = 0
      have hd0 : (Matrix.diagonal (fun i => (d i : ℂ))).mulVec y = 0 := by
        ext i; simpa [Matrix.mulVec_diagonal] using hi i
      rw [hd0, Matrix.mulVec_zero]
  rw [hGH, hSH, hiff, hiff]
  refine forall_congr' fun i => ?_
  simp only [mul_eq_zero, Complex.ofReal_eq_zero, Real.rpow_eq_zero (hσ i) hpm1.ne']

/-! ### Lemma 4(b): Universal Kernel Lifting (Works for ALL p > 1!) -/

/-- General kernel-lifting engine: given any rank-1 upper bound on H ⊕ 0 + ε ṽ ṽᴴ of the form
    (1/p) ‖H ⊕ 0 + ε ṽ ṽᴴ‖_p^p ≤ (1/p) ‖H‖_p^p + ε β + R(ε) with R(ε) / ε → 0,
    any tuple with a unit u ∈ ker(A_k0ᴴ) \ ker(G_Sᴴ) admits an (n+1)-dimensional strict lift! -/
theorem lemma4b_kernel_lifting {m n : ℕ} {p : ℝ} (hp1 : 1 < p)
    (A : Fin m → Mat n)
    (hH_ne : (∑ j, matAbs (A j)) ≠ 0)
    (hmax : ∀ B : Fin m → Mat n, (∑ j, matAbs (B j)) = (∑ j, matAbs (A j)) →
      schattenPow p (∑ j, B j) ≤ schattenPow p (∑ j, A j))
    (k0 : Fin m)
    (u : Fin n → ℂ) (hu_unit : star u ⬝ᵥ u = 1)
    (hu_ker : (A k0)ᴴ.mulVec u = 0)
    (hu_dual : (dualOp p (∑ j, A j))ᴴ.mulVec u ≠ 0) :
    ∃ A' : Fin m → Mat (n + 1), (∑ j, matAbs (A' j)) ≠ 0 ∧ leeRatio p A < leeRatio p A' := by
  have hp0 : 0 < p := by linarith
  have hpm1 : 0 < p - 1 := by linarith
  set S : Mat n := ∑ j, A j
  set H : Mat n := ∑ j, matAbs (A j)
  set G : Mat n := dualOp p S
  set C : ℝ := leeRatio p A
  have hH_psd : H.PosSemidef := by
    have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
      intro s; induction s using Finset.induction_on with
      | empty => simpa using Matrix.PosSemidef.zero
      | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
    exact this Finset.univ
  have hH_norm_pos : 0 < schattenNorm p H := schattenNorm_pos_of_ne_zero hp0 hH_ne
  have hS_ne : S ≠ 0 := by
    intro h0
    have hGH0 : Gᴴ.mulVec u = 0 := by
      have : u ∈ LinearMap.ker (Matrix.mulVecLin Gᴴ) := by
        rw [ker_dualOp_conjTranspose_eq hp1 S]; simp [h0]
      simpa using this
    exact hu_dual hGH0
  have hS_norm_pos : 0 < schattenNorm p S := schattenNorm_pos_of_ne_zero hp0 hS_ne
  have hC_pos : 0 < C := div_pos hS_norm_pos hH_norm_pos
  have hSpow_eq : schattenPow p S = C ^ p * schattenPow p H := by
    rw [← schattenNorm_rpow hp0 S, ← schattenNorm_rpow hp0 H,
      show C = schattenNorm p S / schattenNorm p H from rfl,
      Real.div_rpow hS_norm_pos.le hH_norm_pos.le,
      div_mul_cancel₀ _ (Real.rpow_pos_of_pos hH_norm_pos p).ne']
  -- Step 1: Set g = Gᴴ u ≠ 0, α = ‖g‖ > 0, w = g / α (unit), and note A_k0 w = 0 by Lemma 3!
  let g : Fin n → ℂ := Gᴴ.mulVec u
  let gE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 g
  have hgE_ne : gE ≠ 0 := fun h0 => hu_dual (congrArg WithLp.ofLp h0)
  let α : ℝ := ‖gE‖
  have hα_pos : 0 < α := norm_pos_iff.mpr hgE_ne
  let w : Fin n → ℂ := ((α⁻¹ : ℝ) : ℂ) • g
  have hgg : star g ⬝ᵥ g = ((α ^ 2 : ℝ) : ℂ) := by
    have h1 : star g ⬝ᵥ g = inner ℂ gE gE := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rw [h1, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
  have hw_unit : star w ⬝ᵥ w = 1 := by
    simp only [w, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal, hgg]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    exact_mod_cast (by field_simp [hα_pos.ne'] : α⁻¹ * (α⁻¹ * α ^ 2) = 1)
  have hwg : star w ⬝ᵥ g = (α : ℂ) := by
    simp only [w, star_smul, smul_dotProduct, smul_eq_mul, Complex.star_def, Complex.conj_ofReal, hgg]
    rw [← Complex.ofReal_mul]
    exact_mod_cast (by field_simp [hα_pos.ne'] : α⁻¹ * α ^ 2 = α)
  have hAk0_w : (A k0).mulVec w = 0 := by
    have h1 := lemma3_kernel_map hp1 A hmax k0 u hu_ker
    change (A k0).mulVec g = 0 at h1
    simp only [w, Matrix.mulVec_smul, h1, smul_zero]
  have hPk0_w : (matAbs (A k0)).mulVec w = 0 := by
    have h1 : (star w ⬝ᵥ (matAbs (A k0) * matAbs (A k0)).mulVec w).re = 0 := by
      rw [matAbs_mul_self, ← Matrix.mulVec_mulVec, hAk0_w, Matrix.mulVec_zero, dotProduct_zero,
        Complex.zero_re]
    have h2 : (star ((matAbs (A k0)).mulVec w) ⬝ᵥ (matAbs (A k0)).mulVec w).re = 0 := by
      have hH_eq : (matAbs (A k0))ᴴ = matAbs (A k0) := (matAbs_posSemidef (A k0)).isHermitian.eq
      have h3 : star ((matAbs (A k0)).mulVec w) ⬝ᵥ (matAbs (A k0)).mulVec w =
          star w ⬝ᵥ (matAbs (A k0) * matAbs (A k0)).mulVec w := by
        rw [Matrix.star_mulVec, hH_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
      rw [h3, h1]
    have hE : ‖WithLp.toLp 2 ((matAbs (A k0)).mulVec w)‖ ^ 2 = 0 := by
      have h3 : star ((matAbs (A k0)).mulVec w) ⬝ᵥ (matAbs (A k0)).mulVec w =
          inner ℂ (WithLp.toLp 2 ((matAbs (A k0)).mulVec w)) (WithLp.toLp 2 ((matAbs (A k0)).mulVec w)) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rw [h3, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at h2
      have h4 : (RCLike.ofReal (K := ℂ) (‖WithLp.toLp 2 ((matAbs (A k0)).mulVec w)‖ ^ 2)).re =
          ‖WithLp.toLp 2 ((matAbs (A k0)).mulVec w)‖ ^ 2 := by
        change ((‖WithLp.toLp 2 ((matAbs (A k0)).mulVec w)‖ ^ 2 : ℝ) : ℂ).re = _
        exact Complex.ofReal_re _
      linarith
    have h0 : WithLp.toLp 2 ((matAbs (A k0)).mulVec w) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hE)
    exact congrArg WithLp.ofLp h0
  -- Step 2: Choose mixing angle s ∈ (0, 1/2] with κ := α * s - C^p * β * s^2 > 0
  let β : ℝ := (star w ⬝ᵥ (psdPow (p - 1) H).mulVec w).re
  have hβ_nn : 0 ≤ β := by
    simpa [RCLike.re_to_complex, β] using (psdPow_posSemidef hpm1 hH_psd).re_dotProduct_nonneg w
  let s : ℝ := min (1 / 2) (α / (2 * (C ^ p * β + 1)))
  have hs_pos : 0 < s := lt_min (by norm_num) (div_pos hα_pos (by positivity))
  have hs_le_half : s ≤ 1 / 2 := min_le_left _ _
  have hs_le_ratio : s ≤ α / (2 * (C ^ p * β + 1)) := min_le_right _ _
  let c : ℝ := Real.sqrt (1 - s ^ 2)
  have hsc_sq : s ^ 2 + c ^ 2 = 1 := by
    have h1 : 0 ≤ 1 - s ^ 2 := by nlinarith
    simp [c, Real.sq_sqrt h1]
  let κ : ℝ := α * s - C ^ p * β * s ^ 2
  have hκ_pos : 0 < κ := by
    have hCpβ_nn : 0 ≤ C ^ p * β := mul_nonneg (Real.rpow_nonneg hC_pos.le _) hβ_nn
    have h1 : C ^ p * β * s ≤ α / 2 := by
      calc C ^ p * β * s ≤ (C ^ p * β + 1) * s := by nlinarith
        _ ≤ (C ^ p * β + 1) * (α / (2 * (C ^ p * β + 1))) :=
            mul_le_mul_of_nonneg_left hs_le_ratio (by linarith)
        _ = α / 2 := by field_simp [show C ^ p * β + 1 ≠ 0 by linarith]
    dsimp [κ]; nlinarith
  -- Step 3: Lift u, w to unit vectors uTilde, vTilde ∈ ℂ^(n+1)
  let uTilde : Fin (n + 1) → ℂ := fun i => if hi : i.val < n then u ⟨i.val, hi⟩ else 0
  let vTilde : Fin (n + 1) → ℂ := fun i => if hi : i.val < n then (s : ℂ) * w ⟨i.val, hi⟩ else (c : ℂ)
  have huTilde_unit : star uTilde ⬝ᵥ uTilde = 1 := by
    rw [dotProduct, Fin.sum_univ_castSucc]
    simp only [Pi.star_apply]
    have hlast : star (uTilde (Fin.last n)) * uTilde (Fin.last n) = 0 := by simp [uTilde]
    rw [hlast, add_zero]
    have hsum : ∑ i : Fin n, star (uTilde i.castSucc) * uTilde i.castSucc = star u ⬝ᵥ u := by
      refine Finset.sum_congr rfl fun i _ => by simp [uTilde, i.isLt]
    rw [hsum, hu_unit]
  have hvTilde_unit : star vTilde ⬝ᵥ vTilde = 1 := by
    rw [dotProduct, Fin.sum_univ_castSucc]
    simp only [Pi.star_apply]
    have hlast : star (vTilde (Fin.last n)) * vTilde (Fin.last n) = ((c ^ 2 : ℝ) : ℂ) := by
      simp [vTilde, Complex.conj_ofReal, sq]
    have hsum : ∑ i : Fin n, star (vTilde i.castSucc) * vTilde i.castSucc = ((s ^ 2 : ℝ) : ℂ) := by
      have h1 : ∑ i : Fin n, star (vTilde i.castSucc) * vTilde i.castSucc =
          ((s ^ 2 : ℝ) : ℂ) * (star w ⬝ᵥ w) := by
        rw [dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [vTilde, Fin.val_castSucc, i.isLt, ↓reduceDIte, Pi.star_apply, star_mul',
          Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
        ring
      rw [h1, hw_unit, mul_one]
    rw [hlast, hsum, ← Complex.ofReal_add, hsc_sq, Complex.ofReal_one]
  -- Check orthogonality: (padZero (A k0))ᴴ uTilde = 0 and (padZero (matAbs (A k0))) vTilde = 0
  have hAk0H_uT : (padZero (A k0))ᴴ.mulVec uTilde = 0 := by
    ext i
    rw [padZero_conjTranspose, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
    by_cases hi : i.val < n
    · have hlast : padZero (A k0)ᴴ i (Fin.last n) * uTilde (Fin.last n) = 0 := by simp [uTilde]
      rw [hlast, add_zero]
      have h1 : ∑ j : Fin n, padZero (A k0)ᴴ i j.castSucc * uTilde j.castSucc =
          ((A k0)ᴴ.mulVec u) ⟨i.val, hi⟩ := by
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun j _ => by simp [padZero, uTilde, hi, j.isLt]
      rw [h1, hu_ker]; rfl
    · simp [padZero, hi]
  have hAk0_vT : (padZero (A k0)).mulVec vTilde = 0 := by
    ext i
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
    by_cases hi : i.val < n
    · have hlast : padZero (A k0) i (Fin.last n) * vTilde (Fin.last n) = 0 := by simp [padZero]
      rw [hlast, add_zero]
      have h1 : ∑ j : Fin n, padZero (A k0) i j.castSucc * vTilde j.castSucc =
          (s : ℂ) * ((A k0).mulVec w) ⟨i.val, hi⟩ := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by simp [padZero, vTilde, hi, j.isLt]; ring
      rw [h1, hAk0_w]; simp
    · simp [padZero, hi]
  have hPk0_vT : (padZero (matAbs (A k0))).mulVec vTilde = 0 := by
    ext i
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
    by_cases hi : i.val < n
    · have hlast : padZero (matAbs (A k0)) i (Fin.last n) * vTilde (Fin.last n) = 0 := by simp [padZero]
      rw [hlast, add_zero]
      have h1 : ∑ j : Fin n, padZero (matAbs (A k0)) i j.castSucc * vTilde j.castSucc =
          (s : ℂ) * ((matAbs (A k0)).mulVec w) ⟨i.val, hi⟩ := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by simp [padZero, vTilde, hi, j.isLt]; ring
      rw [h1, hPk0_w]; simp
    · simp [padZero, hi]
  -- Step 4: For any ε > 0, build Aε and verify Sε, Hε, and first-order linear terms!
  have hbuild : ∀ ε : ℝ, 0 < ε →
      let Aε : Fin m → Mat (n + 1) :=
        Function.update (fun j => padZero (A j)) k0 (padZero (A k0) + (ε : ℂ) • outerMat uTilde vTilde)
      (∑ j, Aε j = padZero S + (ε : ℂ) • outerMat uTilde vTilde) ∧
      (∑ j, matAbs (Aε j) = padZero H + (ε : ℂ) • outerMat vTilde vTilde) ∧
      (∑ j, matAbs (Aε j)) ≠ 0 ∧
      ((dualOp p (padZero S))ᴴ * ((ε : ℂ) • outerMat uTilde vTilde)).trace.re = ε * (α * s) ∧
      (star vTilde ⬝ᵥ (psdPow (p - 1) (padZero H)).mulVec vTilde).re = s ^ 2 * β := by
    intro ε hε
    dsimp only
    set Aε : Fin m → Mat (n + 1) :=
      Function.update (fun j => padZero (A j)) k0 (padZero (A k0) + (ε : ℂ) • outerMat uTilde vTilde)
    have hSε : ∑ j, Aε j = padZero S + (ε : ℂ) • outerMat uTilde vTilde := by
      have h1 := Finset.sum_update_of_mem (s := Finset.univ) (Finset.mem_univ k0)
        (fun j => padZero (A j)) (padZero (A k0) + (ε : ℂ) • outerMat uTilde vTilde)
      have h2 := Finset.add_sum_erase Finset.univ (fun j => padZero (A j)) (Finset.mem_univ k0)
      rw [Finset.sdiff_singleton_eq_erase] at h1
      rw [h1, show padZero S = ∑ j, padZero (A j) from (padZero_sum Finset.univ A).symm, ← h2]
      abel
    -- Show |Aε k0| = padZero |A k0| + ε vTilde vTildeᴴ via matAbs_eq_of_posSemidef_sq!
    have hAbs_k0 : matAbs (Aε k0) = padZero (matAbs (A k0)) + (ε : ℂ) • outerMat vTilde vTilde := by
      have hP_psd : (padZero (matAbs (A k0)) + (ε : ℂ) • outerMat vTilde vTilde).PosSemidef := by
        have : (ε : ℂ) • outerMat vTilde vTilde = ε • outerMat vTilde vTilde := by
          ext i j; simp [Complex.real_smul]
        rw [this]; exact (padZero_posSemidef (matAbs_posSemidef (A k0))).add ((outerMat_posSemidef vTilde).smul hε.le)
      refine matAbs_eq_of_posSemidef_sq hP_psd ?_
      have hAεk0 : Aε k0 = padZero (A k0) + (ε : ℂ) • outerMat uTilde vTilde :=
        Function.update_self k0 _ _
      rw [hAεk0, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
      have houtH : (outerMat uTilde vTilde)ᴴ = outerMat vTilde uTilde := by
        ext i j; simp only [outerMat, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul',
          star_star]; ring
      rw [houtH]
      -- Cross terms vanish!
      have hc1 : (padZero (A k0))ᴴ * outerMat uTilde vTilde = 0 := by
        ext i j
        have hi := congr_fun hAk0H_uT i
        simp only [Matrix.mul_apply, outerMat, Matrix.of_apply, Matrix.mulVec, dotProduct,
          Pi.zero_apply, Matrix.zero_apply] at hi ⊢
        have : ∑ k, (padZero (A k0))ᴴ i k * (uTilde k * star (vTilde j)) =
            (∑ k, (padZero (A k0))ᴴ i k * uTilde k) * star (vTilde j) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring
        rw [this, hi, zero_mul]
      have hc2 : outerMat vTilde uTilde * padZero (A k0) = 0 := by
        have := congrArg Matrix.conjTranspose hc1
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, houtH,
          Matrix.conjTranspose_zero] at this
        exact this
      have hc3 : padZero (matAbs (A k0)) * outerMat vTilde vTilde = 0 := by
        ext i j
        have hi := congr_fun hPk0_vT i
        simp only [Matrix.mul_apply, outerMat, Matrix.of_apply, Matrix.mulVec, dotProduct,
          Pi.zero_apply, Matrix.zero_apply] at hi ⊢
        have : ∑ k, padZero (matAbs (A k0)) i k * (vTilde k * star (vTilde j)) =
            (∑ k, padZero (matAbs (A k0)) i k * vTilde k) * star (vTilde j) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring
        rw [this, hi, zero_mul]
      have hc4 : outerMat vTilde vTilde * padZero (matAbs (A k0)) = 0 := by
        have := congrArg Matrix.conjTranspose hc3
        rw [Matrix.conjTranspose_mul, (outerMat_posSemidef vTilde).isHermitian.eq,
          (padZero_posSemidef (matAbs_posSemidef (A k0))).isHermitian.eq, Matrix.conjTranspose_zero] at this
        exact this
      have hsq_out1 : outerMat vTilde uTilde * outerMat uTilde vTilde = outerMat vTilde vTilde := by
        ext i j; simp only [Matrix.mul_apply, outerMat, Matrix.of_apply]
        have : ∑ k, vTilde i * star (uTilde k) * (uTilde k * star (vTilde j)) =
            vTilde i * star (vTilde j) * (star uTilde ⬝ᵥ uTilde) := by
          simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [this, huTilde_unit, mul_one]
      have hsq_out2 : outerMat vTilde vTilde * outerMat vTilde vTilde = outerMat vTilde vTilde := by
        ext i j; simp only [Matrix.mul_apply, outerMat, Matrix.of_apply]
        have : ∑ k, vTilde i * star (vTilde k) * (vTilde k * star (vTilde j)) =
            vTilde i * star (vTilde j) * (star vTilde ⬝ᵥ vTilde) := by
          simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [this, hvTilde_unit, mul_one]
      have hsq_main : (padZero (A k0))ᴴ * padZero (A k0) = padZero (matAbs (A k0)) * padZero (matAbs (A k0)) := by
        rw [padZero_conjTranspose, ← padZero_mul, ← padZero_mul, matAbs_mul_self]
      symm
      calc ((padZero (A k0))ᴴ + (ε : ℂ) • outerMat vTilde uTilde) *
              (padZero (A k0) + (ε : ℂ) • outerMat uTilde vTilde)
          = (padZero (A k0))ᴴ * padZero (A k0) + (ε : ℂ) • ((padZero (A k0))ᴴ * outerMat uTilde vTilde) +
            ((ε : ℂ) • (outerMat vTilde uTilde * padZero (A k0)) +
              ((ε : ℂ) * (ε : ℂ)) • (outerMat vTilde uTilde * outerMat uTilde vTilde)) := by
              rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
                Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = padZero (matAbs (A k0)) * padZero (matAbs (A k0)) +
              ((ε : ℂ) * (ε : ℂ)) • outerMat vTilde vTilde := by
              rw [hc1, hc2, hsq_out1, hsq_main, smul_zero, add_zero, zero_add]
        _ = (padZero (matAbs (A k0)) + (ε : ℂ) • outerMat vTilde vTilde) *
              (padZero (matAbs (A k0)) + (ε : ℂ) • outerMat vTilde vTilde) := by
              rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
                Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc3, hc4, hsq_out2, smul_zero,
                add_zero, zero_add]
    have hHε : ∑ j, matAbs (Aε j) = padZero H + (ε : ℂ) • outerMat vTilde vTilde := by
      have h1 := Finset.sum_update_of_mem (s := Finset.univ) (Finset.mem_univ k0)
        (fun j => matAbs (padZero (A j))) (matAbs (Aε k0))
      have hfun : (fun j => matAbs (Aε j)) =
          Function.update (fun j => matAbs (padZero (A j))) k0 (matAbs (Aε k0)) := by
        ext j a b; by_cases hjk : j = k0
        · subst hjk; rw [Function.update_self]
        · rw [Function.update_of_ne hjk]; dsimp [Aε]; rw [Function.update_of_ne hjk]
      rw [hfun, h1, Finset.sdiff_singleton_eq_erase, hAbs_k0]
      have h2 := Finset.add_sum_erase Finset.univ (fun j => matAbs (padZero (A j))) (Finset.mem_univ k0)
      have h3 : ∑ j, matAbs (padZero (A j)) = padZero H := by
        simp_rw [matAbs_padZero]; exact padZero_sum Finset.univ (fun j => matAbs (A j))
      rw [← h3, ← h2, matAbs_padZero]; abel
    have hHε_ne : (∑ j, matAbs (Aε j)) ≠ 0 := by
      intro h0
      have htr := congrArg (fun M : Mat (n + 1) => M.trace.re) h0
      rw [hHε, Matrix.trace_add, Matrix.trace_smul, Complex.add_re, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Matrix.trace_zero, Complex.zero_re] at htr
      have htr_pad : 0 ≤ (padZero H).trace.re := by
        simpa using re_trace_mul_nonneg_of_posSemidef (padZero_posSemidef hH_psd) Matrix.PosSemidef.one
      have htr_out : (outerMat vTilde vTilde).trace.re = 1 := by
        have := trace_mul_outerMat (1 : Mat (n + 1)) vTilde
        simp only [Matrix.one_mul, Matrix.one_mulVec] at this
        rw [this, hvTilde_unit, Complex.one_re]
      rw [htr_out] at htr; linarith
    have hlin_S : ((dualOp p (padZero S))ᴴ * ((ε : ℂ) • outerMat uTilde vTilde)).trace.re = ε * (α * s) := by
      rw [dualOp_padZero hp1 S, padZero_conjTranspose, Matrix.mul_smul, Matrix.trace_smul,
        smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      have htr : (padZero Gᴴ * outerMat uTilde vTilde).trace = star vTilde ⬝ᵥ (padZero Gᴴ).mulVec uTilde := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, outerMat, Matrix.of_apply,
          dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [htr, dotProduct, Fin.sum_univ_castSucc]
      simp only [Pi.star_apply]
      have hlast : star (vTilde (Fin.last n)) * ((padZero Gᴴ).mulVec uTilde) (Fin.last n) = 0 := by
        simp [Matrix.mulVec, dotProduct, padZero]
      rw [hlast, add_zero]
      have hsum : ∑ i : Fin n, star (vTilde i.castSucc) * ((padZero Gᴴ).mulVec uTilde) i.castSucc =
          (s : ℂ) * (star w ⬝ᵥ g) := by
        rw [dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hmv : ((padZero Gᴴ).mulVec uTilde) i.castSucc = g i := by
          rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
          have hl : padZero Gᴴ i.castSucc (Fin.last n) * uTilde (Fin.last n) = 0 := by simp [uTilde]
          rw [hl, add_zero]
          simp only [g, Matrix.mulVec, dotProduct]
          refine Finset.sum_congr rfl fun j _ => by simp [padZero, uTilde, i.isLt, j.isLt]
        rw [hmv]
        simp only [vTilde, Fin.val_castSucc, i.isLt, ↓reduceDIte, Pi.star_apply, star_mul',
          Complex.star_def, Complex.conj_ofReal]; ring
      rw [hsum, hwg, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
    have hlin_H : (star vTilde ⬝ᵥ (psdPow (p - 1) (padZero H)).mulVec vTilde).re = s ^ 2 * β := by
      rw [psdPow_padZero hpm1 hH_psd, dotProduct, Fin.sum_univ_castSucc]
      simp only [Pi.star_apply]
      have hlast : star (vTilde (Fin.last n)) * ((padZero (psdPow (p - 1) H)).mulVec vTilde) (Fin.last n) = 0 := by
        simp [Matrix.mulVec, dotProduct, padZero]
      rw [hlast, add_zero]
      have hsum : ∑ i : Fin n, star (vTilde i.castSucc) * ((padZero (psdPow (p - 1) H)).mulVec vTilde) i.castSucc =
          ((s ^ 2 : ℝ) : ℂ) * (star w ⬝ᵥ (psdPow (p - 1) H).mulVec w) := by
        rw [dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hmv : ((padZero (psdPow (p - 1) H)).mulVec vTilde) i.castSucc =
            (s : ℂ) * ((psdPow (p - 1) H).mulVec w) i := by
          rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
          have hl : padZero (psdPow (p - 1) H) i.castSucc (Fin.last n) * vTilde (Fin.last n) = 0 := by
            simp [padZero]
          rw [hl, add_zero]
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by simp [padZero, vTilde, i.isLt, j.isLt]; ring
        rw [hmv]
        simp only [vTilde, Fin.val_castSucc, i.isLt, ↓reduceDIte, Pi.star_apply, star_mul',
          Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]; ring
      rw [hsum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact ⟨hSε, hHε, hHε_ne, hlin_S, hlin_H⟩
  -- Step 5: Split p < 2 (Lemma 4(a)) vs p ≥ 2 (C² Taylor bound with lo = 0)!
  by_cases hp2 : p < 2
  · -- Subquadratic case 1 < p < 2: use Lemma 4(a) with ε = min 1 ((p * κ / (2 * C^p)) ^ (p - 1)⁻¹)
    let ε : ℝ := min 1 ((p * κ / (2 * C ^ p)) ^ (p - 1)⁻¹)
    have hε_pos : 0 < ε := lt_min zero_lt_one (Real.rpow_pos_of_pos (div_pos (by positivity) (by positivity)) _)
    set Aε : Fin m → Mat (n + 1) :=
      Function.update (fun j => padZero (A j)) k0 (padZero (A k0) + (ε : ℂ) • outerMat uTilde vTilde)
    obtain ⟨hSε, hHε, hHε_ne, hlin_S, hlin_H⟩ := hbuild ε hε_pos
    change ∑ j, Aε j = padZero S + (ε : ℂ) • outerMat uTilde vTilde at hSε
    change ∑ j, matAbs (Aε j) = padZero H + (ε : ℂ) • outerMat vTilde vTilde at hHε
    change (∑ j, matAbs (Aε j)) ≠ 0 at hHε_ne
    refine ⟨Aε, hHε_ne, ?_⟩
    have hS_lb := prop0_subgradient_bound hp1 (padZero S) (∑ j, Aε j)
    have hsub : (∑ j, Aε j) - padZero S = (ε : ℂ) • outerMat uTilde vTilde := by rw [hSε]; abel
    rw [hsub, hlin_S, schattenPow_padZero hp0 S] at hS_lb
    have hH_ub := lemma4a_rank_one_smoothness hp1 hp2 (padZero_posSemidef hH_psd) vTilde hvTilde_unit hε_pos.le
    rw [← hHε, hlin_H, schattenPow_padZero hp0 H] at hH_ub
    have hCp_pos : 0 < C ^ p := Real.rpow_pos_of_pos hC_pos p
    have hε_pow_le : ε ^ (p - 1) ≤ p * κ / (2 * C ^ p) := by
      calc ε ^ (p - 1) ≤ ((p * κ / (2 * C ^ p)) ^ (p - 1)⁻¹) ^ (p - 1) :=
            Real.rpow_le_rpow hε_pos.le (min_le_right _ _) hpm1.le
        _ = p * κ / (2 * C ^ p) := by
            rw [← Real.rpow_mul (div_nonneg (by positivity) (by positivity)),
              inv_mul_cancel₀ hpm1.ne', Real.rpow_one]
    have hεp_eq : ε ^ p = ε * ε ^ (p - 1) := by
      calc ε ^ p = ε ^ (1 + (p - 1)) := by ring_nf
        _ = ε ^ (1 : ℝ) * ε ^ (p - 1) := Real.rpow_add hε_pos 1 (p - 1)
        _ = ε * ε ^ (p - 1) := by rw [Real.rpow_one]
    have hrem_lt : C ^ p * ((1 / p) * ε ^ p) < ε * κ := by
      rw [hεp_eq]
      have h1 : C ^ p * ((1 / p) * (ε * ε ^ (p - 1))) ≤ C ^ p * ((1 / p) * (ε * (p * κ / (2 * C ^ p)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hε_pow_le hε_pos.le) (by positivity)) hCp_pos.le
      have h2 : C ^ p * ((1 / p) * (ε * (p * κ / (2 * C ^ p)))) = (1 / 2) * (ε * κ) := by
        field_simp [hp0.ne', hCp_pos.ne']
      linarith [mul_pos hε_pos hκ_pos]
    have hpow_gt : C ^ p * schattenPow p (∑ j, matAbs (Aε j)) < schattenPow p (∑ j, Aε j) := by
      have hmul := mul_le_mul_of_nonneg_left hH_ub hCp_pos.le
      have hdiff : (1 / p) * (C ^ p * schattenPow p (∑ j, matAbs (Aε j))) <
          (1 / p) * schattenPow p (∑ j, Aε j) := by
        have hκ_eq : ε * (α * s) - C ^ p * (ε * (s ^ 2 * β)) = ε * κ := by dsimp [κ]; ring
        have h1 : (1 / p) * (C ^ p * schattenPow p (∑ j, matAbs (Aε j))) =
            C ^ p * ((1 / p) * schattenPow p (∑ j, matAbs (Aε j))) := by ring
        have h2 : (1 / p) * schattenPow p S = C ^ p * ((1 / p) * schattenPow p H) := by
          rw [hSpow_eq]; ring
        linarith only [hmul, hS_lb, hrem_lt, hκ_eq, h1, h2]
      exact lt_of_mul_lt_mul_left hdiff (one_div_pos.mpr hp0).le
    have hHε_norm_pos : 0 < schattenNorm p (∑ j, matAbs (Aε j)) := schattenNorm_pos_of_ne_zero hp0 hHε_ne
    have hSε_norm_gt : C * schattenNorm p (∑ j, matAbs (Aε j)) < schattenNorm p (∑ j, Aε j) := by
      by_contra hle; push Not at hle
      have := Real.rpow_le_rpow (schattenNorm_nonneg p _) hle hp0.le
      rw [schattenNorm_rpow hp0, Real.mul_rpow hC_pos.le hHε_norm_pos.le, schattenNorm_rpow hp0] at this
      linarith only [hpow_gt, this]
    show C < schattenNorm p (∑ j, Aε j) / schattenNorm p (∑ j, matAbs (Aε j))
    exact (lt_div_iff₀ hHε_norm_pos).mpr hSε_norm_gt
  · -- Superquadratic case p ≥ 2 (Proposition 5): use C² Taylor bound with lo = 0!
    push Not at hp2
    let hi : ℝ := (padZero H).trace.re + 1
    have hHpad_tr_nn : 0 ≤ (padZero H).trace.re := by
      simpa using re_trace_mul_nonneg_of_posSemidef (padZero_posSemidef hH_psd) Matrix.PosSemidef.one
    have hhi_pos : 0 < hi := by dsimp [hi]; linarith
    let K : ℝ := (p - 1) * hi ^ (p - 2)
    have hK_nn : 0 ≤ K := mul_nonneg hpm1.le (Real.rpow_nonneg hhi_pos.le _)
    let ε : ℝ := min 1 (κ / (2 * (C ^ p * K + 1)))
    have hε_pos : 0 < ε := lt_min zero_lt_one (div_pos hκ_pos (by positivity))
    have hε_le1 : ε ≤ 1 := min_le_left _ _
    set Aε : Fin m → Mat (n + 1) :=
      Function.update (fun j => padZero (A j)) k0 (padZero (A k0) + (ε : ℂ) • outerMat uTilde vTilde)
    obtain ⟨hSε, hHε, hHε_ne, hlin_S, hlin_H⟩ := hbuild ε hε_pos
    change ∑ j, Aε j = padZero S + (ε : ℂ) • outerMat uTilde vTilde at hSε
    change ∑ j, matAbs (Aε j) = padZero H + (ε : ℂ) • outerMat vTilde vTilde at hHε
    change (∑ j, matAbs (Aε j)) ≠ 0 at hHε_ne
    refine ⟨Aε, hHε_ne, ?_⟩
    have hS_lb := prop0_subgradient_bound hp1 (padZero S) (∑ j, Aε j)
    have hsub : (∑ j, Aε j) - padZero S = (ε : ℂ) • outerMat uTilde vTilde := by rw [hSε]; abel
    rw [hsub, hlin_S, schattenPow_padZero hp0 S] at hS_lb
    have hHε_psd : (padZero H + (ε : ℂ) • outerMat vTilde vTilde).PosSemidef := by
      have : (ε : ℂ) • outerMat vTilde vTilde = ε • outerMat vTilde vTilde := by
        ext i j; simp [Complex.real_smul]
      rw [this]; exact (padZero_posSemidef hH_psd).add ((outerMat_posSemidef vTilde).smul hε_pos.le)
    have hK_bound : ∀ c ∈ Set.Icc (0 : ℝ) hi, |(p - 1) * c ^ (p - 2)| ≤ K := by
      intro x hx
      rw [abs_of_nonneg (mul_nonneg hpm1.le (Real.rpow_nonneg hx.1 _))]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.1 hx.2 (by linarith)) hpm1.le
    have hX_eig : ∀ i, (padZero_posSemidef hH_psd).isHermitian.eigenvalues i ∈ Set.Icc (0 : ℝ) hi := fun i =>
      ⟨(padZero_posSemidef hH_psd).eigenvalues_nonneg i,
        (posSemidef_eigenvalues_le_trace (padZero_posSemidef hH_psd) i).trans (by dsimp [hi]; linarith)⟩
    have hY_eig : ∀ j, hHε_psd.isHermitian.eigenvalues j ∈ Set.Icc (0 : ℝ) hi := fun j => by
      have htr : (padZero H + (ε : ℂ) • outerMat vTilde vTilde).trace.re = (padZero H).trace.re + ε := by
        rw [Matrix.trace_add, Matrix.trace_smul, Complex.add_re, smul_eq_mul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im]
        have htr1 : (outerMat vTilde vTilde).trace.re = 1 := by
          have := trace_mul_outerMat (1 : Mat (n + 1)) vTilde
          simp only [Matrix.one_mul, Matrix.one_mulVec] at this
          rw [this, hvTilde_unit, Complex.one_re]
        rw [htr1]; ring
      exact ⟨hHε_psd.eigenvalues_nonneg j,
        (posSemidef_eigenvalues_le_trace hHε_psd j).trans (by rw [htr]; dsimp [hi]; linarith)⟩
    have htb := matrix_schattenPow_taylor_bound hp1 le_rfl hhi_pos.le hK_bound (Or.inr hp2)
      (padZero_posSemidef hH_psd) hHε_psd hX_eig hY_eig
    have hdiff_H : (padZero H + (ε : ℂ) • outerMat vTilde vTilde) - padZero H =
        (ε : ℂ) • outerMat vTilde vTilde := by abel
    have htr_lin : (psdPow (p - 1) (padZero H) *
        ((padZero H + (ε : ℂ) • outerMat vTilde vTilde) - padZero H)).trace.re = ε * (s ^ 2 * β) := by
      rw [hdiff_H, Matrix.mul_smul, Matrix.trace_smul, trace_mul_outerMat, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hlin_H]; ring
    have htr_sq : (((padZero H + (ε : ℂ) • outerMat vTilde vTilde) - padZero H) *
        ((padZero H + (ε : ℂ) • outerMat vTilde vTilde) - padZero H)).trace.re = ε ^ 2 := by
      rw [hdiff_H, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul]
      have hout_sq : outerMat vTilde vTilde * outerMat vTilde vTilde = outerMat vTilde vTilde := by
        ext i j; simp only [Matrix.mul_apply, outerMat, Matrix.of_apply]
        have : ∑ k, vTilde i * star (vTilde k) * (vTilde k * star (vTilde j)) =
            vTilde i * star (vTilde j) * (star vTilde ⬝ᵥ vTilde) := by
          simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [this, hvTilde_unit, mul_one]
      have htr1 : (outerMat vTilde vTilde).trace = 1 := by
        have := trace_mul_outerMat (1 : Mat (n + 1)) vTilde
        simp only [Matrix.one_mul, Matrix.one_mulVec] at this
        rw [this, hvTilde_unit]
      rw [hout_sq, htr1, smul_eq_mul, mul_one, ← sq, ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [htr_lin, htr_sq, ← hHε, schattenPow_padZero hp0 H] at htb
    have hH_ub : (1 / p) * schattenPow p (∑ j, matAbs (Aε j)) ≤
        (1 / p) * schattenPow p H + ε * (s ^ 2 * β) + K * ε ^ 2 := by
      linarith [(abs_le.mp htb).2]
    have hCp_pos : 0 < C ^ p := Real.rpow_pos_of_pos hC_pos p
    have hrem_lt : C ^ p * (K * ε ^ 2) < ε * κ := by
      have hCpK_nn : 0 ≤ C ^ p * K := mul_nonneg hCp_pos.le hK_nn
      have h1 : C ^ p * K * ε ≤ κ / 2 := by
        calc C ^ p * K * ε ≤ (C ^ p * K + 1) * ε := mul_le_mul_of_nonneg_right (by linarith) hε_pos.le
          _ ≤ (C ^ p * K + 1) * (κ / (2 * (C ^ p * K + 1))) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
          _ = κ / 2 := by field_simp [show C ^ p * K + 1 ≠ 0 by linarith]
      have h2 : C ^ p * (K * ε ^ 2) = (C ^ p * K * ε) * ε := by ring
      rw [h2]
      have h3 : (C ^ p * K * ε) * ε ≤ (κ / 2) * ε := mul_le_mul_of_nonneg_right h1 hε_pos.le
      linarith [mul_pos hε_pos hκ_pos]
    have hpow_gt : C ^ p * schattenPow p (∑ j, matAbs (Aε j)) < schattenPow p (∑ j, Aε j) := by
      have hmul := mul_le_mul_of_nonneg_left hH_ub hCp_pos.le
      have hdiff : (1 / p) * (C ^ p * schattenPow p (∑ j, matAbs (Aε j))) <
          (1 / p) * schattenPow p (∑ j, Aε j) := by
        have hκ_eq : ε * (α * s) - C ^ p * (ε * (s ^ 2 * β)) = ε * κ := by dsimp [κ]; ring
        have h1 : (1 / p) * (C ^ p * schattenPow p (∑ j, matAbs (Aε j))) =
            C ^ p * ((1 / p) * schattenPow p (∑ j, matAbs (Aε j))) := by ring
        have h2 : (1 / p) * schattenPow p S = C ^ p * ((1 / p) * schattenPow p H) := by
          rw [hSpow_eq]; ring
        linarith only [hmul, hS_lb, hrem_lt, hκ_eq, h1, h2]
      exact lt_of_mul_lt_mul_left hdiff (one_div_pos.mpr hp0).le
    have hHε_norm_pos : 0 < schattenNorm p (∑ j, matAbs (Aε j)) := schattenNorm_pos_of_ne_zero hp0 hHε_ne
    have hSε_norm_gt : C * schattenNorm p (∑ j, matAbs (Aε j)) < schattenNorm p (∑ j, Aε j) := by
      by_contra hle; push Not at hle
      have := Real.rpow_le_rpow (schattenNorm_nonneg p _) hle hp0.le
      rw [schattenNorm_rpow hp0, Real.mul_rpow hC_pos.le hHε_norm_pos.le, schattenNorm_rpow hp0] at this
      linarith only [hpow_gt, this]
    show C < schattenNorm p (∑ j, Aε j) / schattenNorm p (∑ j, matAbs (Aε j))
    exact (lt_div_iff₀ hHε_norm_pos).mpr hSε_norm_gt

/-! ### Rank-Nullity Helper: finrank(ker Mᴴ) = finrank(ker M) -/

lemma finrank_ker_conjTranspose_eq {n : ℕ} (M : Mat n) :
    Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin Mᴴ)) =
      Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin M)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin Mᴴ)
  have hrank : Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin Mᴴ)) =
      Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin M)) :=
    Matrix.rank_conjTranspose M
  omega

/-- Helper: If A is a maximizer with C > 1 and ker(S) ∩ ran(H) = {0}, then for every k
    there exists a unit u ∈ ker(A_kᴴ) \ ker((dualOp p S)ᴴ). -/
lemma exists_unit_ker_not_ker_dualOp {m n : ℕ} {p : ℝ} (hp1 : 1 < p)
    (A : Fin m → Mat n)
    (hH_ne : (∑ j, matAbs (A j)) ≠ 0)
    (hC_gt : 1 < leeRatio p A)
    (hmax : ∀ B : Fin m → Mat n, (∑ j, matAbs (B j)) ≠ 0 → leeRatio p B ≤ leeRatio p A)
    (hinj : ∀ z : Fin n → ℂ, z ∈ LinearMap.range (Matrix.mulVecLin (∑ j, matAbs (A j))) →
      (∑ j, A j).mulVec z = 0 → z = 0)
    (k0 : Fin m) :
    ∃ u : Fin n → ℂ, star u ⬝ᵥ u = 1 ∧ (A k0)ᴴ.mulVec u = 0 ∧
      (dualOp p (∑ j, A j))ᴴ.mulVec u ≠ 0 := by
  set S : Mat n := ∑ j, A j
  set H : Mat n := ∑ j, matAbs (A j)
  have hH_psd : H.PosSemidef := by
    have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
      intro s; induction s using Finset.induction_on with
      | empty => simpa using Matrix.PosSemidef.zero
      | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
    exact this Finset.univ
  have hkerH_le_Ak : ∀ j : Fin m,
      LinearMap.ker (Matrix.mulVecLin H) ≤ LinearMap.ker (Matrix.mulVecLin (A j)) := by
    intro j x hx
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
    have hsum0 : ∑ i : Fin m, (star x ⬝ᵥ (matAbs (A i)).mulVec x).re = 0 := by
      have h1 : (star x ⬝ᵥ H.mulVec x).re = 0 := by rw [hx, dotProduct_zero, Complex.zero_re]
      rw [← h1]; simp only [H, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    have hnn : ∀ i : Fin m, 0 ≤ (star x ⬝ᵥ (matAbs (A i)).mulVec x).re := fun i => by
      simpa [RCLike.re_to_complex] using (matAbs_posSemidef (A i)).re_dotProduct_nonneg x
    have hj0 : (star x ⬝ᵥ (matAbs (A j)).mulVec x).re = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp hsum0 j (Finset.mem_univ j)
    have hPj0 : (matAbs (A j)).mulVec x = 0 :=
      posSemidef_mulVec_eq_zero_of_re_dotProduct_eq_zero (matAbs_posSemidef (A j)) x hj0
    have hAx_sq : (star ((A j).mulVec x) ⬝ᵥ (A j).mulVec x).re = 0 := by
      have h1 : star ((A j).mulVec x) ⬝ᵥ (A j).mulVec x = star x ⬝ᵥ ((A j)ᴴ * A j).mulVec x := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
      rw [h1, ← matAbs_mul_self, ← Matrix.mulVec_mulVec, hPj0, Matrix.mulVec_zero,
        dotProduct_zero, Complex.zero_re]
    have hE : ‖WithLp.toLp 2 ((A j).mulVec x)‖ ^ 2 = 0 := by
      have h1 : star ((A j).mulVec x) ⬝ᵥ (A j).mulVec x =
          inner ℂ (WithLp.toLp 2 ((A j).mulVec x)) (WithLp.toLp 2 ((A j).mulVec x)) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rw [h1, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at hAx_sq
      have h2 : (RCLike.ofReal (K := ℂ) (‖WithLp.toLp 2 ((A j).mulVec x)‖ ^ 2)).re =
          ‖WithLp.toLp 2 ((A j).mulVec x)‖ ^ 2 := by
        change ((‖WithLp.toLp 2 ((A j).mulVec x)‖ ^ 2 : ℝ) : ℂ).re = _
        exact Complex.ofReal_re _
      linarith
    exact congrArg WithLp.ofLp (norm_eq_zero.mp (sq_eq_zero_iff.mp hE))
  have hkerH_eq_kerS : LinearMap.ker (Matrix.mulVecLin S) = LinearMap.ker (Matrix.mulVecLin H) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
      let V : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := LinearMap.range (Matrix.toEuclideanLin H)
      let xE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
      let x1E : EuclideanSpace ℂ (Fin n) := V.starProjection xE
      let x2E : EuclideanSpace ℂ (Fin n) := xE - x1E
      have hx2_orth : x2E ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal xE
      have hHx2 : H.mulVec x2E.ofLp = 0 := by
        have h1 : ∀ y : EuclideanSpace ℂ (Fin n), inner ℂ (Matrix.toEuclideanLin H y) x2E = 0 := fun y =>
          Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self _ y) hx2_orth
        have h2 : Matrix.toEuclideanLin H x2E = 0 := by
          apply ext_inner_left ℂ; intro y
          have hadj : (Matrix.toEuclideanLin H).adjoint = Matrix.toEuclideanLin H := by
            rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hH_psd.isHermitian.eq]
          rw [inner_zero_right, ← hadj, LinearMap.adjoint_inner_right, h1 y]
        exact congrArg WithLp.ofLp h2
      have hSx2 : S.mulVec x2E.ofLp = 0 := by
        change (∑ j, A j).mulVec x2E.ofLp = 0
        rw [Matrix.sum_mulVec]
        exact Finset.sum_eq_zero fun j _ => hkerH_le_Ak j hHx2
      have hx1_ran : x1E.ofLp ∈ LinearMap.range (Matrix.mulVecLin H) := by
        obtain ⟨y, hy⟩ := Submodule.starProjection_apply_mem V xE
        exact ⟨y.ofLp, congrArg WithLp.ofLp hy⟩
      have hSx1 : S.mulVec x1E.ofLp = 0 := by
        have hsplit : x = x1E.ofLp + x2E.ofLp := by
          ext i; simp [xE, x2E]
        rw [hsplit, Matrix.mulVec_add, hSx2, add_zero] at hx
        exact hx
      have hx1_zero : x1E.ofLp = 0 := hinj x1E.ofLp hx1_ran hSx1
      have hx_eq : x = x2E.ofLp := by
        have hsplit : x = x1E.ofLp + x2E.ofLp := by ext i; simp [xE, x2E]
        rw [hsplit, hx1_zero, zero_add]
      rw [hx_eq]; exact hHx2
    · intro x hx
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
      change (∑ j, A j).mulVec x = 0
      rw [Matrix.sum_mulVec]
      exact Finset.sum_eq_zero fun j _ => hkerH_le_Ak j hx
  -- By Lemma 1, ∃ v ≠ 0 in ran(H) ∩ ker(A k0); since ran(H) ∩ ker(H) = {0}, ker(H) < ker(A k0)!
  obtain ⟨v, hv_ne, hv_ran, hv_Ak0⟩ := lemma1_universal_rank_deficiency hp1 A hH_ne hC_gt hmax k0
  have hv_not_kerH : v ∉ LinearMap.ker (Matrix.mulVecLin H) := by
    intro hker
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
    obtain ⟨y, hy⟩ := hv_ran
    change H.mulVec y = v at hy
    have h0 : star v ⬝ᵥ v = 0 := by
      calc star v ⬝ᵥ v = star (H.mulVec y) ⬝ᵥ v := by rw [hy]
        _ = star y ⬝ᵥ H.mulVec v := by
            rw [Matrix.star_mulVec, hH_psd.isHermitian.eq, ← Matrix.dotProduct_mulVec]
        _ = 0 := by rw [hker, dotProduct_zero]
    have hE : ‖WithLp.toLp 2 v‖ ^ 2 = 0 := by
      have h1 : star v ⬝ᵥ v = inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 v) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rw [h1, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at h0
      exact (RCLike.ofReal_eq_zero (K := ℂ)).mp h0
    exact hv_ne (congrArg WithLp.ofLp (norm_eq_zero.mp (sq_eq_zero_iff.mp hE)))
  have hlt_ker : LinearMap.ker (Matrix.mulVecLin H) < LinearMap.ker (Matrix.mulVecLin (A k0)) :=
    lt_of_le_of_ne (hkerH_le_Ak k0) fun heq => hv_not_kerH (heq ▸ hv_Ak0)
  have hfin_lt : Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin (dualOp p S)ᴴ)) <
      Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin (A k0)ᴴ)) := by
    rw [ker_dualOp_conjTranspose_eq hp1 S, finrank_ker_conjTranspose_eq S,
      finrank_ker_conjTranspose_eq (A k0), hkerH_eq_kerS]
    exact Submodule.finrank_lt_finrank_of_lt hlt_ker
  have hnot_le : ¬ (LinearMap.ker (Matrix.mulVecLin (A k0)ᴴ) ≤
      LinearMap.ker (Matrix.mulVecLin (dualOp p S)ᴴ)) := fun hle =>
    not_lt_of_ge (Submodule.finrank_mono hle) hfin_lt
  rw [SetLike.not_le_iff_exists] at hnot_le
  obtain ⟨u0, hu0_mem, hu0_not⟩ := hnot_le
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hu0_mem hu0_not
  have hu0_ne : u0 ≠ 0 := fun h0 => hu0_not (by rw [h0, Matrix.mulVec_zero])
  let u0E : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 u0
  have hu0_norm_pos : 0 < ‖u0E‖ := norm_pos_iff.mpr fun h0 => hu0_ne (congrArg WithLp.ofLp h0)
  let u : Fin n → ℂ := ((‖u0E‖⁻¹ : ℝ) : ℂ) • u0
  refine ⟨u, ?_, ?_, ?_⟩
  · have h1 : star u0 ⬝ᵥ u0 = ((‖u0E‖ ^ 2 : ℝ) : ℂ) := by
      have h2 : star u0 ⬝ᵥ u0 = inner ℂ u0E u0E := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rw [h2, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
    simp only [u, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal, h1]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    exact_mod_cast (by field_simp [hu0_norm_pos.ne'] : ‖u0E‖⁻¹ * (‖u0E‖⁻¹ * ‖u0E‖ ^ 2) = 1)
  · simp only [u, Matrix.mulVec_smul, hu0_mem, smul_zero]
  · simp only [u, Matrix.mulVec_smul]
    intro h0
    have := smul_eq_zero.mp h0
    rcases this with hc | hv
    · exact (Complex.ofReal_ne_zero.mpr (inv_ne_zero hu0_norm_pos.ne')) hc
    · exact hu0_not hv

/-! ### Proposition 5 (Superquadratic Obstruction for p ≥ 2) & Theorem 1 (Strict Hierarchy) -/

/-- Proposition 5 (Superquadratic Obstruction): For EVERY p > 1 (in particular p ≥ 2),
    m ≥ 2, n ≥ 2, any tuple A attaining C_{p,m}(n) = C_{p,m}(n+1) (for instance any global
    maximizer attaining C_{p,m}(∞) in dimension n) MUST satisfy ker(S) ∩ ran(H) ≠ {0}! -/
theorem prop5_superquadratic_obstruction {m n : ℕ} {p : ℝ} (hp1 : 1 < p) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (A : Fin m → Mat n)
    (hH_ne : (∑ j, matAbs (A j)) ≠ 0)
    (hC_eq : leeRatio p A = leeConst p m n)
    (hflat : leeConst p m (n + 1) ≤ leeConst p m n) :
    ∃ z : Fin n → ℂ, z ≠ 0 ∧ z ∈ LinearMap.range (Matrix.mulVecLin (∑ j, matAbs (A j))) ∧
      (∑ j, A j).mulVec z = 0 := by
  have hp0 : 0 < p := by linarith
  have hC_gt : 1 < leeRatio p A := by
    rw [hC_eq]
    have h2 : 1 < leeConst p m 2 := one_lt_leeConst_two hp1 hm
    have hmono : ∀ k : ℕ, 2 ≤ k → leeConst p m 2 ≤ leeConst p m k := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        by_cases hk2 : k = 1
        · subst hk2; exact le_rfl
        · exact (ih (by omega)).trans (leeConst_mono hp1 (by omega) (by omega))
    exact lt_of_lt_of_le h2 (hmono n hn)
  have hmax : ∀ B : Fin m → Mat n, (∑ j, matAbs (B j)) ≠ 0 → leeRatio p B ≤ leeRatio p A := by
    intro B hB
    rw [hC_eq, leeConst]
    exact le_csSup (leeConst_bddAbove hp1) ⟨B, hB, rfl⟩
  have hmax_polar : ∀ B : Fin m → Mat n, (∑ j, matAbs (B j)) = (∑ j, matAbs (A j)) →
      schattenPow p (∑ j, B j) ≤ schattenPow p (∑ j, A j) := by
    intro B hB
    have hle := hmax B (hB ▸ hH_ne)
    have hH_pos : 0 < schattenNorm p (∑ j, matAbs (A j)) := schattenNorm_pos_of_ne_zero hp0 hH_ne
    have hnorm_le : schattenNorm p (∑ j, B j) ≤ schattenNorm p (∑ j, A j) := by
      simp only [leeRatio, hB] at hle
      exact (div_le_div_iff_of_pos_right hH_pos).mp hle
    rw [← schattenNorm_rpow hp0, ← schattenNorm_rpow hp0]
    exact Real.rpow_le_rpow (schattenNorm_nonneg p _) hnorm_le hp0.le
  by_contra hnone
  push Not at hnone
  have hinj : ∀ z : Fin n → ℂ, z ∈ LinearMap.range (Matrix.mulVecLin (∑ j, matAbs (A j))) →
      (∑ j, A j).mulVec z = 0 → z = 0 := by
    intro z hz_ran hz_ker
    by_contra hz_ne
    exact hnone z hz_ne hz_ran hz_ker
  let k0 : Fin m := ⟨0, by omega⟩
  obtain ⟨u, hu_unit, hu_ker, hu_dual⟩ :=
    exists_unit_ker_not_ker_dualOp hp1 A hH_ne hC_gt hmax hinj k0
  obtain ⟨A', hA'_ne, hlt⟩ := lemma4b_kernel_lifting hp1 A hH_ne hmax_polar k0 u hu_unit hu_ker hu_dual
  have hle_next : leeRatio p A' ≤ leeConst p m (n + 1) :=
    le_csSup (leeConst_bddAbove hp1) ⟨A', hA'_ne, rfl⟩
  linarith

/-- Theorem 1 (Strict Infinite-Dimensional Hierarchy for 1 < p < 2):
    For every 1 < p < 2, m ≥ 2, and n ≥ 1, C_{p,m}(n) < C_{p,m}(n + 1). -/
theorem theorem1_strict_hierarchy {m n : ℕ} {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hm : 2 ≤ m) (hn : 1 ≤ n) :
    leeConst p m n < leeConst p m (n + 1) := by
  by_cases hn1 : n = 1
  · subst hn1
    rw [leeConst_one_eq_one hp1 (by omega)]
    exact one_lt_leeConst_two hp1 hm
  · have hn2 : 2 ≤ n := by omega
    have hp0 : 0 < p := by linarith
    obtain ⟨A, hH_ne, hC_eq, _⟩ := exists_leeConst_maximizer (m := m) (n := n) hp1 (by omega) hn
    by_contra hnot
    push Not at hnot
    obtain ⟨z, hz_ne, hz_ran, hz_ker⟩ :=
      prop5_superquadratic_obstruction hp1 hm hn2 A hH_ne hC_eq hnot
    have hS_ne : (∑ j, A j) ≠ 0 := by
      have hC_gt : 1 < leeRatio p A := by
        rw [hC_eq]
        have h2 : 1 < leeConst p m 2 := one_lt_leeConst_two hp1 hm
        have hmono : ∀ k : ℕ, 2 ≤ k → leeConst p m 2 ≤ leeConst p m k := by
          intro k hk
          induction k with
          | zero => omega
          | succ k ih =>
            by_cases hk2 : k = 1
            · subst hk2; exact le_rfl
            · exact (ih (by omega)).trans (leeConst_mono hp1 (by omega) (by omega))
        exact lt_of_lt_of_le h2 (hmono n hn2)
      intro h0
      have h0' : leeRatio p A = 0 := by simp [leeRatio, h0, schattenNorm_zero hp0]
      linarith
    obtain ⟨A', hA'_ne, hlt⟩ := lemma2_full_rank_sum hp1 hp2 A hS_ne hH_ne z hz_ne hz_ran hz_ker
    have hle_next : leeRatio p A' ≤ leeConst p m (n + 1) :=
      le_csSup (leeConst_bddAbove hp1) ⟨A', hA'_ne, rfl⟩
    linarith

/-- Theorem 1 (No Finite-Dimensional Extremizer):
    For every 1 < p < 2, m ≥ 2, and n ≥ 1, C_{p,m}(n) < C_{p,m}(∞). -/
theorem theorem1_no_finite_extremizer {m n : ℕ} {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hm : 2 ≤ m) (hn : 1 ≤ n) :
    leeConst p m n < leeConstInf p m := by
  have hstep : leeConst p m n < leeConst p m (n + 1) := theorem1_strict_hierarchy hp1 hp2 hm hn
  have hbdd : BddAbove { r : ℝ | ∃ k : ℕ, 1 ≤ k ∧ r = leeConst p m k } := by
    refine ⟨(m : ℝ), ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    refine csSup_le ?_ ?_
    · obtain ⟨A, hA, _, _⟩ := exists_leeConst_maximizer (m := m) (n := k) hp1 (by omega) hk
      exact ⟨leeRatio p A, A, hA, rfl⟩
    · rintro _ ⟨A, _, rfl⟩
      exact leeRatio_le_card hp1 A
  have hle : leeConst p m (n + 1) ≤ leeConstInf p m := by
    unfold leeConstInf
    exact le_csSup hbdd ⟨n + 1, by omega, rfl⟩
  exact lt_of_lt_of_le hstep hle

end MI20
