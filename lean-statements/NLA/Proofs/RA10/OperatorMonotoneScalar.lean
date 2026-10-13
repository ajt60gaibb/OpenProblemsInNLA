import NLA.Proofs.RA10.SpectralQuadratic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Scalar consequences of the frozen all-size real matrix hypothesis.
The two-dimensional argument is the scalar case of Hansen, Theorem 2.1
(arXiv:1112.0098). It uses the continuity already present in `AdmissibleFunction`.
This is preparation for the positive Löwner representation, not that theorem. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open NLA.Statements.RA10

namespace NLA.Proofs.RA10

/-- Dimension one of the frozen hypothesis gives ordinary monotonicity. -/
theorem operatorMonotoneOnNonnegative_monotoneOn {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnNonnegative f) : MonotoneOn f (Set.Ici 0) := by
  intro x hx y hy hxy
  have hs (t : ℝ) (ht : 0 ≤ t) :
      OrderedPSDSpectralDecomposition (fun _ _ : Fin 1 => t)
        (fun _ => t) (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    refine ⟨fun _ => ht, fun _ _ _ => le_rfl, ?_, ?_⟩
    · intro i j
      fin_cases i; fin_cases j
      simp [Matrix.one_apply]
    · ext i j
      fin_cases i; fin_cases j
      simp [SpectralMatrix]
  have hdiff : PositiveSemidefinite ((fun _ _ : Fin 1 => y) - (fun _ _ => x)) := by
    refine ⟨fun _ _ => rfl, ?_⟩
    intro v
    simp only [Fin.sum_univ_one]
    change 0 ≤ v 0 * (y - x) * v 0
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sq_nonneg (v 0))]
  have h := (hf 1 (by omega) _ _ _ _ _ _ (hs y hy) (hs x hx) hdiff).2
    (fun _ => 1)
  simpa [FunctionMatrix, SpectralMatrix] using h

private def rotation (p q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![p, -q; q, p]

private theorem rotation_orthogonal {p q : ℝ} (hpq : p ^ 2 + q ^ 2 = 1) :
    ∀ i j, ∑ l, rotation p q l i * rotation p q l j = if i = j then 1 else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rotation, Fin.sum_univ_two] <;> nlinarith

private theorem spectral_rotation (x y p q : ℝ) :
    SpectralMatrix ![x, y] (rotation p q) =
      !![x * p ^ 2 + y * q ^ 2, (x - y) * p * q;
        (x - y) * p * q, x * q ^ 2 + y * p ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpectralMatrix, rotation, Fin.sum_univ_two] <;> ring

private theorem pair_antitone {x y : ℝ} (hyx : y ≤ x) : Antitone ![x, y] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- The upper-left corner of a two-dimensional comparison. No differentiability
or strict positivity of the scalar arguments is assumed. -/
private theorem operatorMonotone_jensen_approx {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnNonnegative f)
    {x y t δ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hδ : 0 < δ) :
    t * f x + (1 - t) * f y ≤ f (t * x + (1 - t) * y + δ) := by
  let p := Real.sqrt t
  let q := Real.sqrt (1 - t)
  have hp : p ^ 2 = t := Real.sq_sqrt ht
  have hq : q ^ 2 = 1 - t := Real.sq_sqrt (sub_nonneg.mpr ht1)
  have hpq : p ^ 2 + q ^ 2 = 1 := by rw [hp, hq]; ring
  let z := x * p ^ 2 + y * q ^ 2
  let w := x * q ^ 2 + y * p ^ 2
  let d := (x - y) * p * q
  let L := w + d ^ 2 / δ + z + δ
  have hz : 0 ≤ z := add_nonneg (mul_nonneg hx (sq_nonneg _))
    (mul_nonneg hy (sq_nonneg _))
  have hw : 0 ≤ w := add_nonneg (mul_nonneg hx (sq_nonneg _))
    (mul_nonneg hy (sq_nonneg _))
  have hdz : 0 ≤ d ^ 2 / δ := div_nonneg (sq_nonneg _) hδ.le
  have hL : z + δ ≤ L := by dsimp [L]; linarith
  let G := SpectralMatrix ![x, y] (rotation p q)
  let H := SpectralMatrix ![L, z + δ] (rotation 0 1)
  have hG : OrderedPSDSpectralDecomposition G ![x, y] (rotation p q) := by
    refine ⟨?_, pair_antitone hyx, rotation_orthogonal hpq, rfl⟩
    intro i
    fin_cases i <;> simp [hx, hy]
  have hH : OrderedPSDSpectralDecomposition H ![L, z + δ] (rotation 0 1) := by
    refine ⟨?_, pair_antitone hL, rotation_orthogonal (by norm_num), rfl⟩
    intro i
    fin_cases i
    · change 0 ≤ L
      linarith
    · change 0 ≤ z + δ
      linarith
  have hmat : H - G = !![δ, -d; -d, L - w] := by
    dsimp [H, G]
    rw [spectral_rotation, spectral_rotation]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [z, w, d]
  have hdiff : PositiveSemidefinite (H - G) := by
    rw [hmat]
    refine ⟨?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> simp
    · intro v
      simp only [Fin.sum_univ_two]
      have hid : δ * (v 0 * δ * v 0 + v 0 * -d * v 1 +
          (v 1 * -d * v 0 + v 1 * (L - w) * v 1)) =
          (δ * v 0 - d * v 1) ^ 2 + δ * (z + δ) * (v 1) ^ 2 := by
        dsimp [L]
        field_simp
        ring
      exact nonneg_of_mul_nonneg_right
        (hid.symm ▸ add_nonneg (sq_nonneg _)
          (mul_nonneg (mul_nonneg hδ.le (by linarith)) (sq_nonneg _))) hδ
  have h := (hf 2 (by omega) H G _ _ _ _ hH hG hdiff).2 ![1, 0]
  have hfG : FunctionMatrix f ![x, y] (rotation p q) =
      SpectralMatrix ![f x, f y] (rotation p q) := by rfl
  have hfH : FunctionMatrix f ![L, z + δ] (rotation 0 1) =
      SpectralMatrix ![f L, f (z + δ)] (rotation 0 1) := by rfl
  rw [hfG, hfH, spectral_rotation, spectral_rotation] at h
  simp [Fin.sum_univ_two, hp, hq] at h
  dsimp [z] at h
  rw [hp, hq] at h
  simpa only [mul_comm] using h

/-- Every admissible function is scalar concave on the entire closed half-line.
The comparison uses dimension two, followed by continuity at the convex combination. -/
theorem admissibleFunction_concaveOn {f : ℝ → ℝ} (hf : AdmissibleFunction f) :
    ConcaveOn ℝ (Set.Ici 0) f := by
  have hj {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x)
      (ht : 0 ≤ t) (ht1 : t ≤ 1) :
      t * f x + (1 - t) * f y ≤ f (t * x + (1 - t) * y) := by
    let z := t * x + (1 - t) * y
    have hz : 0 ≤ z := add_nonneg (mul_nonneg ht hx)
      (mul_nonneg (sub_nonneg.mpr ht1) hy)
    have hlim : Filter.Tendsto (fun δ : ℝ => f (z + δ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (f z)) := by
      apply (hf.1 z hz).tendsto.comp
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · have hid : Filter.Tendsto (fun δ : ℝ => δ)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
          Filter.tendsto_id.mono_left nhdsWithin_le_nhds
        simpa only [add_zero] using Filter.Tendsto.const_add z hid
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact add_nonneg hz (le_of_lt hδ)
    exact ge_of_tendsto hlim (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact operatorMonotone_jensen_approx hf.2.2 hx hy hyx ht ht1 hδ)
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  rcases le_total y x with hyx | hxy
  · simpa [hb'] using hj hx hy hyx ha ha1
  · have h := hj hy hx hxy hb (show b ≤ 1 by linarith)
    have ha' : a = 1 - b := by linarith
    simpa [← ha', add_comm] using h

/-- The sharp elementary bounds needed to normalize the positive class and
bound it in the topology of pointwise convergence. -/
theorem admissibleFunction_bounds {f : ℝ → ℝ} (hf : AdmissibleFunction f)
    {x : ℝ} (hx : 0 ≤ x) :
    min 1 x * f 1 ≤ f x ∧ f x ≤ max 1 x * f 1 := by
  have hm := operatorMonotoneOnNonnegative_monotoneOn hf.2.2
  have hc := admissibleFunction_concaveOn hf
  have hf0 := hf.2.1 0 le_rfl
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1, max_eq_left hx1, one_mul]
    refine ⟨?_, hm hx (by norm_num) hx1⟩
    have h := hc.2 (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
      (show (0 : ℝ) ∈ Set.Ici 0 by simp) hx (sub_nonneg.mpr hx1)
      (show x + (1 - x) = 1 by ring)
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero] at h
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) hf0]
  · have hxpos : 0 < x := by linarith
    rw [min_eq_left (by linarith), max_eq_right (by linarith), one_mul]
    refine ⟨hm (by norm_num) hx (by linarith), ?_⟩
    have hinv : 0 ≤ 1 / x := le_of_lt (one_div_pos.mpr hxpos)
    have hinv1 : 1 / x ≤ 1 := (div_le_one hxpos).mpr (by linarith)
    have h := hc.2 hx (show (0 : ℝ) ∈ Set.Ici 0 by simp) hinv
      (sub_nonneg.mpr hinv1) (show 1 / x + (1 - 1 / x) = 1 by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, one_div_mul_cancel hxpos.ne'] at h
    have hmul := mul_le_mul_of_nonneg_left h hx
    have hcancel : x * (1 / x * f x) = f x := by field_simp
    nlinarith [mul_nonneg hx (mul_nonneg (sub_nonneg.mpr hinv1) hf0)]

/-- Normalization loses only the identically zero function on the relevant domain. -/
theorem admissibleFunction_eq_zero_of_one_eq_zero {f : ℝ → ℝ}
    (hf : AdmissibleFunction f) (h1 : f 1 = 0) {x : ℝ} (hx : 0 ≤ x) :
    f x = 0 := by
  have h := (admissibleFunction_bounds hf hx).2
  rw [h1, mul_zero] at h
  exact le_antisymm h (hf.2.1 x hx)

theorem admissibleFunction_pos_of_one_pos {f : ℝ → ℝ}
    (hf : AdmissibleFunction f) (h1 : 0 < f 1) {x : ℝ} (hx : 0 < x) :
    0 < f x :=
  lt_of_lt_of_le (mul_pos (lt_min (by norm_num) hx) h1)
    (admissibleFunction_bounds hf hx.le).1

#assert_trust kernel operatorMonotoneOnNonnegative_monotoneOn
#assert_trust kernel operatorMonotone_jensen_approx
#assert_trust kernel admissibleFunction_concaveOn
#assert_trust kernel admissibleFunction_bounds
#assert_trust kernel admissibleFunction_eq_zero_of_one_eq_zero
#assert_trust kernel admissibleFunction_pos_of_one_pos
#print axioms admissibleFunction_bounds

end NLA.Proofs.RA10
