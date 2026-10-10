import Mathlib
import LeanCert.Tactic.Verification
import NLA.Proofs.MF03.CosineProduct

/-! The independently reviewed dense-set Euler cosine product bridge for MF-03. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Real Topology

namespace NLA.Proofs.MF03

/-- The frozen factorial series specializes to the complex cosine series. -/
theorem waveSeries_neg_pi_sq_eq_cos (w : ℂ) :
    waveSeries (-(((Real.pi : ℂ) * w) ^ 2)) =
      Complex.cos ((Real.pi : ℂ) * w) := by
  unfold waveSeries
  rw [Complex.cos_eq_tsum]
  congr 1
  funext j
  rw [neg_pow, pow_mul]

private noncomputable def sineEulerFactor (w : ℂ) (j : ℕ) : ℂ :=
  1 - w ^ 2 / (((j + 1 : ℕ) : ℂ) ^ 2)

private noncomputable def sineEulerProduct (N : ℕ) (w : ℂ) : ℂ :=
  ∏ j ∈ Finset.range N, sineEulerFactor w j

private theorem prod_even_odd (f : ℕ → ℂ) (N : ℕ) :
    (∏ j ∈ Finset.range (2 * N), f j) =
      (∏ k ∈ Finset.range N, f (2 * k)) *
        (∏ k ∈ Finset.range N, f (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hindex : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
      calc
        (∏ j ∈ Finset.range (2 * (N + 1)), f j) =
            (∏ j ∈ Finset.range (2 * N), f j) * f (2 * N) * f (2 * N + 1) := by
          rw [hindex, Finset.prod_range_succ, Finset.prod_range_succ]
        _ = ((∏ k ∈ Finset.range N, f (2 * k)) *
            (∏ k ∈ Finset.range N, f (2 * k + 1))) *
              f (2 * N) * f (2 * N + 1) := by rw [ih]
        _ = (∏ k ∈ Finset.range (N + 1), f (2 * k)) *
            (∏ k ∈ Finset.range (N + 1), f (2 * k + 1)) := by
          rw [Finset.prod_range_succ, Finset.prod_range_succ]
          ring

private theorem sineEulerFactor_even (w : ℂ) (k : ℕ) :
    sineEulerFactor (2 * w) (2 * k + 1) = sineEulerFactor w k := by
  unfold sineEulerFactor
  have hcast : (((2 * k + 1 + 1 : ℕ) : ℂ)) =
      2 * (((k + 1 : ℕ) : ℂ)) := by
    push_cast
    ring
  rw [hcast]
  have hk : (((k + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  field_simp [hk]

private theorem cosineFactor_pi_sq (k : ℕ) :
    cosineFactor (k + 1) * Real.pi ^ 2 =
      4 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hk : (((2 * k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hhalf : (((k + 1 : ℕ) : ℝ) - 1 / 2) =
      (((2 * k + 1 : ℕ) : ℝ)) / 2 := by
    push_cast
    ring
  unfold cosineFactor
  rw [hhalf]
  field_simp [hpi, hk]
  ring

private theorem sineEulerFactor_odd (w : ℂ) (k : ℕ) :
    sineEulerFactor (2 * w) (2 * k) =
      (1 : ℂ) + (cosineFactor (k + 1) : ℂ) *
        (-(((Real.pi : ℂ) * w) ^ 2)) := by
  have hfactor : (cosineFactor (k + 1) : ℂ) * (Real.pi : ℂ) ^ 2 =
      (4 : ℂ) / (((2 * k + 1 : ℕ) : ℂ) ^ 2) := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) (cosineFactor_pi_sq k)
    simpa using h
  unfold sineEulerFactor
  calc
    (1 : ℂ) - (2 * w) ^ 2 / (((2 * k + 1 : ℕ) : ℂ) ^ 2) =
        1 - ((4 : ℂ) / (((2 * k + 1 : ℕ) : ℂ) ^ 2)) * w ^ 2 := by ring
    _ = 1 + (cosineFactor (k + 1) : ℂ) *
        (-(((Real.pi : ℂ) * w) ^ 2)) := by rw [← hfactor]; ring

private theorem sineEuler_even_odd_split (N : ℕ) (w : ℂ) :
    sineEulerProduct (2 * N) (2 * w) =
      sineEulerProduct N w *
        cosinePartialProduct N (-(((Real.pi : ℂ) * w) ^ 2)) := by
  calc
    sineEulerProduct (2 * N) (2 * w) =
        (∏ k ∈ Finset.range N, sineEulerFactor (2 * w) (2 * k)) *
          (∏ k ∈ Finset.range N, sineEulerFactor (2 * w) (2 * k + 1)) := by
      exact prod_even_odd (sineEulerFactor (2 * w)) N
    _ = cosinePartialProduct N (-(((Real.pi : ℂ) * w) ^ 2)) *
        sineEulerProduct N w := by
      congr 1
      · unfold cosinePartialProduct
        apply Finset.prod_congr rfl
        intro k hk
        exact sineEulerFactor_odd w k
      · unfold sineEulerProduct
        apply Finset.prod_congr rfl
        intro k hk
        exact sineEulerFactor_even w k
    _ = sineEulerProduct N w *
        cosinePartialProduct N (-(((Real.pi : ℂ) * w) ^ 2)) := by ring

private theorem sineEuler_tendsto (w : ℂ) :
    Filter.Tendsto
      (fun N : ℕ => (Real.pi : ℂ) * w * sineEulerProduct N w)
      Filter.atTop (nhds (Complex.sin ((Real.pi : ℂ) * w))) := by
  simpa [sineEulerProduct, sineEulerFactor] using
    Complex.tendsto_euler_sin_prod w

/-- On the nonzero-sine set, the finite odd Euler products converge to the
exact factorial wave series at the matching quadratic argument. -/
theorem cosinePartialProduct_tendsto_waveSeries_of_sin_ne_zero
    (w : ℂ)
    (hw : Complex.sin ((Real.pi : ℂ) * w) ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ =>
        cosinePartialProduct N (-(((Real.pi : ℂ) * w) ^ 2)))
      Filter.atTop
      (nhds (waveSeries (-(((Real.pi : ℂ) * w) ^ 2)))) := by
  let B : ℕ → ℂ := fun N => (Real.pi : ℂ) * w * sineEulerProduct N w
  let A : ℕ → ℂ := fun N =>
    (Real.pi : ℂ) * (2 * w) * sineEulerProduct (2 * N) (2 * w)
  let C : ℕ → ℂ := fun N =>
    cosinePartialProduct N (-(((Real.pi : ℂ) * w) ^ 2))
  have hB : Filter.Tendsto B Filter.atTop
      (nhds (Complex.sin ((Real.pi : ℂ) * w))) := sineEuler_tendsto w
  have hdouble : Filter.Tendsto (fun N : ℕ => 2 * N)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop' (by norm_num : 0 < (2 : ℕ))
  have hA : Filter.Tendsto A Filter.atTop
      (nhds (Complex.sin ((Real.pi : ℂ) * (2 * w)))) := by
    exact (sineEuler_tendsto (2 * w)).comp hdouble
  have hfinite (N : ℕ) : A N = C N * (2 * B N) := by
    dsimp [A, B, C]
    rw [sineEuler_even_odd_split]
    ring
  have hsin2 : Complex.sin ((Real.pi : ℂ) * (2 * w)) =
      Complex.cos ((Real.pi : ℂ) * w) *
        (2 * Complex.sin ((Real.pi : ℂ) * w)) := by
    have harg : (Real.pi : ℂ) * (2 * w) =
        2 * ((Real.pi : ℂ) * w) := by ring
    rw [harg, Complex.sin_two_mul]
    ring
  have htwo : Filter.Tendsto (fun N : ℕ => 2 * B N) Filter.atTop
      (nhds (2 * Complex.sin ((Real.pi : ℂ) * w))) :=
    tendsto_const_nhds.mul hB
  have htwone : (2 : ℂ) * Complex.sin ((Real.pi : ℂ) * w) ≠ 0 :=
    mul_ne_zero (by norm_num) hw
  have hproduct : Filter.Tendsto (fun N : ℕ => C N * (2 * B N))
      Filter.atTop
      (nhds (Complex.cos ((Real.pi : ℂ) * w) *
        (2 * Complex.sin ((Real.pi : ℂ) * w)))) := by
    rw [hsin2] at hA
    have hfun : (fun N : ℕ => C N * (2 * B N)) = A := by
      funext N
      exact (hfinite N).symm
    rw [hfun]
    exact hA
  have hC : Filter.Tendsto C Filter.atTop
      (nhds (Complex.cos ((Real.pi : ℂ) * w))) :=
    (Filter.tendsto_mul_iff_of_ne_zero htwo htwone).mp hproduct
  rw [waveSeries_neg_pi_sq_eq_cos]
  exact hC

#assert_trust kernel waveSeries_neg_pi_sq_eq_cos
#assert_trust kernel cosinePartialProduct_tendsto_waveSeries_of_sin_ne_zero
#print axioms cosinePartialProduct_tendsto_waveSeries_of_sin_ne_zero

end NLA.Proofs.MF03
