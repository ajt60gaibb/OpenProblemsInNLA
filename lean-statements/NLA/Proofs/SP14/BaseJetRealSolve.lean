import NLA.Proofs.SP14.BaseJetPencilFormula

/-!
The actual real first-jet equations for the exterior base symbol and
one restored negative packet. This is the unperturbed finite stage only.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Polynomial

namespace NLA.Proofs.SP14

noncomputable def baseJetPad (h q : ℕ) (_hh : h ≤ q)
    (u : Fin h → ℝ) (d : Fin q) : ℂ :=
  if hd : d.val < h then (u ⟨d.val, hd⟩ : ℂ) else 0

noncomputable def baseJetRealMap (m q h : ℕ) (hh : h ≤ q)
    (u : Fin h → ℝ) (k : Fin h) : ℝ :=
  ((oddJetPolynomial
      (baseJetSymbol m q (baseJetPad h q hh u)) m).coeff k.val).re

private theorem baseJetPad_sum (h q : ℕ) (hh : h ≤ q)
    (u : Fin h → ℝ) (f : ℕ → ℂ) :
    (∑ d : Fin q, baseJetPad h q hh u d * f d.val) =
      ∑ d : Fin h, (u d : ℂ) * f d.val := by
  classical
  let g : ℕ → ℂ := fun d => if hd : d < h then (u ⟨d, hd⟩ : ℂ) * f d else 0
  have hqsum : (∑ d : Fin q, baseJetPad h q hh u d * f d.val) =
      ∑ d ∈ Finset.range q, g d := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro d hd
    have hdq : d < q := Finset.mem_range.mp hd
    simp [g, baseJetPad, hdq]
  have hhsum : (∑ d : Fin h, (u d : ℂ) * f d.val) =
      ∑ d ∈ Finset.range h, g d := by
    simp [Finset.sum_fin_eq_sum_range, g]
  rw [hqsum, hhsum]
  have hsubset : Finset.range h ⊆ Finset.range q := by
    intro d hd
    simp only [Finset.mem_range] at hd ⊢
    omega
  symm
  apply Finset.sum_subset hsubset
  intro d hd hdnot
  have hnot : ¬ d < h := by
    simp only [Finset.mem_range] at hdnot
    exact hdnot
  simp [g, hnot]

private theorem baseJet_inner_coeff (d k : ℕ) :
    (∑ r ∈ Finset.range (d + 1),
      Polynomial.C (((r + 1 : ℕ) : ℂ) * baseCoeff (d - r)) *
        Polynomial.X ^ r).coeff k =
      if k ≤ d then ((k + 1 : ℕ) : ℂ) * baseCoeff (d - k) else 0 := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases hkd : k ≤ d
  · rw [Finset.sum_eq_single k]
    · simp [hkd]
    · intro r hr hrk
      have hne : k ≠ r := Ne.symm hrk
      simp [hne]
    · intro hnot
      have hmem : k ∈ Finset.range (d + 1) := by
        simp only [Finset.mem_range]
        omega
      exact (hnot hmem).elim
  · rw [Finset.sum_eq_zero]
    · simp [hkd]
    · intro r hr
      have hne : k ≠ r := by
        have hrle : r ≤ d := by
          simp only [Finset.mem_range] at hr
          omega
        omega
      simp [hne]

private theorem baseJetPolynomial_coeff_low (m q h : ℕ)
    (hq : 2 * q ≤ m + 1) (hh : h ≤ q)
    (u : Fin h → ℝ) (k : Fin h) :
    (oddJetPolynomial (baseJetSymbol m q (baseJetPad h q hh u)) m).coeff k.val =
      -2 * ∑ d : Fin q,
        baseJetPad h q hh u d *
          (if k.val ≤ d.val then
            ((k.val + 1 : ℕ) : ℂ) * baseCoeff (d.val - k.val) else 0) := by
  have hkm : k.val ≠ m := by
    have hk := k.isLt
    omega
  rw [baseJetPolynomial_formula m q hq]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
    if_neg hkm, Polynomial.coeff_ofNat_mul]
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul, baseJet_inner_coeff]
  ring

/-- The actual complex coefficient is the complexification of the displayed
real source matrix applied to the selected variables. -/
theorem baseJetPolynomial_coeff_eq_mulVec (m q h : ℕ)
    (hq : 2 * q ≤ m + 1) (hh : h ≤ q)
    (u : Fin h → ℝ) (k : Fin h) :
    (oddJetPolynomial (baseJetSymbol m q (baseJetPad h q hh u)) m).coeff k.val =
      (((baseJetMatrix h).mulVec u k : ℝ) : ℂ) := by
  calc
    (oddJetPolynomial (baseJetSymbol m q (baseJetPad h q hh u)) m).coeff k.val =
        -2 * ∑ d : Fin h, (u d : ℂ) *
          (if k.val ≤ d.val then
            ((k.val + 1 : ℕ) : ℂ) * baseCoeff (d.val - k.val) else 0) := by
      rw [baseJetPolynomial_coeff_low m q h hq hh u k]
      congr 1
      exact baseJetPad_sum h q hh u (fun n =>
        if k.val ≤ n then ((k.val + 1 : ℕ) : ℂ) * baseCoeff (n - k.val) else 0)
    _ = ∑ d : Fin h, ((baseJetMatrix h k d : ℝ) : ℂ) * (u d : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hkd : k.val ≤ d.val
      · have hkfin : k ≤ d := hkd
        simp only [baseJetMatrix, if_pos hkfin, if_pos hkd]
        push_cast [baseCoeffReal_to_complex]
        ring
      · have hkfin : ¬ k ≤ d := hkd
        simp [baseJetMatrix, hkfin, hkd]
    _ = (((baseJetMatrix h).mulVec u k : ℝ) : ℂ) := by
      rw [Matrix.mulVec_apply_eq_sum]
      push_cast
      rfl

theorem baseJetPolynomial_coeff_real (m q h : ℕ)
    (hq : 2 * q ≤ m + 1) (hh : h ≤ q)
    (u : Fin h → ℝ) (k : Fin h) :
    ((oddJetPolynomial (baseJetSymbol m q (baseJetPad h q hh u)) m).coeff k.val).im = 0 := by
  rw [baseJetPolynomial_coeff_eq_mulVec m q h hq hh u k]
  simp

theorem baseJetRealMap_eq_mulVec (m q h : ℕ)
    (hq : 2 * q ≤ m + 1) (hh : h ≤ q) :
    baseJetRealMap m q h hh = (baseJetMatrix h).mulVec := by
  funext u k
  unfold baseJetRealMap
  rw [baseJetPolynomial_coeff_eq_mulVec m q h hq hh u k]
  simp

noncomputable def baseJetVector (m q h : ℕ)
    (_hq : 2 * q ≤ m + 1) (hh : h ≤ q)
    (y : Fin h → ℝ) : Fin q → ℂ :=
  baseJetPad h q hh (baseJetSolve h y)

theorem baseJetVector_spec (m q h : ℕ)
    (hq : 2 * q ≤ m + 1) (hh : h ≤ q)
    (y : Fin h → ℝ) :
    ∀ k : Fin h,
      (oddJetPolynomial
        (baseJetSymbol m q (baseJetVector m q h hq hh y)) m).coeff k.val =
          (y k : ℂ) := by
  intro k
  unfold baseJetVector
  rw [baseJetPolynomial_coeff_eq_mulVec m q h hq hh]
  rw [baseJetSolve_spec]

theorem baseJetVector_zero_jet (m q h : ℕ)
    (hq : 2 * q ≤ m + 1) (hh : h ≤ q) :
    JetVanishing (baseJetSymbol m q (baseJetVector m q h hq hh 0)) m h := by
  intro d hd
  let k : Fin h := ⟨d, hd⟩
  have hk := baseJetVector_spec m q h hq hh 0 k
  simpa [k] using hk

/-- Uniqueness in the selected first `h` real coordinates. Other source
coordinates are fixed to zero by `baseJetPad`. -/
theorem baseJetVector_unique_selected (m q h : ℕ)
    (hq : 2 * q ≤ m + 1) (hh : h ≤ q)
    (y u : Fin h → ℝ)
    (hu : ∀ k : Fin h,
      (oddJetPolynomial (baseJetSymbol m q (baseJetPad h q hh u)) m).coeff k.val =
        (y k : ℂ)) :
    u = baseJetSolve h y := by
  have hm : (baseJetMatrix h).mulVec u = y := by
    funext k
    apply Complex.ofReal_injective
    calc
      (((baseJetMatrix h).mulVec u k : ℝ) : ℂ) =
          (oddJetPolynomial (baseJetSymbol m q (baseJetPad h q hh u)) m).coeff k.val :=
        (baseJetPolynomial_coeff_eq_mulVec m q h hq hh u k).symm
      _ = (y k : ℂ) := hu k
  have hunit : IsUnit (baseJetMatrix h).det :=
    isUnit_iff_ne_zero.mpr (baseJetMatrix_det_ne_zero h)
  calc
    u = (baseJetMatrix h)⁻¹.mulVec ((baseJetMatrix h).mulVec u) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
    _ = baseJetSolve h y := by rw [hm]; rfl

theorem baseJetRealMap_difference (m q h : ℕ)
    (hq : 2 * q ≤ m + 1) (hh : h ≤ q)
    (u u' : Fin h → ℝ) :
    baseJetRealMap m q h hh u' - baseJetRealMap m q h hh u =
      (baseJetMatrix h).mulVec (u' - u) := by
  rw [baseJetRealMap_eq_mulVec m q h hq hh]
  exact (Matrix.mulVec_sub (baseJetMatrix h) u' u).symm

theorem baseJetRealMap_hasFDerivAt (m q h : ℕ)
    (hq : 2 * q ≤ m + 1) (hh : h ≤ q)
    (u : Fin h → ℝ) :
    HasFDerivAt (baseJetRealMap m q h hh)
      (baseJetMatrix h).mulVecLin.toContinuousLinearMap u := by
  rw [baseJetRealMap_eq_mulVec m q h hq hh]
  simpa only [LinearMap.coe_toContinuousLinearMap', Matrix.coe_mulVecLin] using
    ((baseJetMatrix h).mulVecLin.toContinuousLinearMap).hasFDerivAt

theorem baseJetRealMap_fderiv (m q h : ℕ)
    (hq : 2 * q ≤ m + 1) (hh : h ≤ q)
    (u : Fin h → ℝ) :
    fderiv ℝ (baseJetRealMap m q h hh) u =
      (baseJetMatrix h).mulVecLin.toContinuousLinearMap := by
  exact (baseJetRealMap_hasFDerivAt m q h hq hh u).fderiv

theorem baseJetRealMap_fderiv_bijective (m q h : ℕ)
    (hq : 2 * q ≤ m + 1) (hh : h ≤ q)
    (u : Fin h → ℝ) :
    Function.Bijective (fderiv ℝ (baseJetRealMap m q h hh) u) := by
  rw [baseJetRealMap_fderiv m q h hq hh u]
  have hunit : IsUnit (baseJetMatrix h).det :=
    isUnit_iff_ne_zero.mpr (baseJetMatrix_det_ne_zero h)
  constructor
  · intro x y hxy
    have hxy' : (baseJetMatrix h).mulVec x = (baseJetMatrix h).mulVec y := by
      simpa only [LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply] using hxy
    have hinv := congrArg ((baseJetMatrix h)⁻¹.mulVec) hxy'
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
      Matrix.one_mulVec] using hinv
  · intro y
    refine ⟨baseJetSolve h y, ?_⟩
    simpa only [LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply] using
      baseJetSolve_spec h y

#assert_trust kernel baseJetPolynomial_coeff_eq_mulVec
#assert_trust kernel baseJetVector_spec
#assert_trust kernel baseJetVector_zero_jet
#assert_trust kernel baseJetVector_unique_selected
#assert_trust kernel baseJetRealMap_fderiv_bijective
#print axioms baseJetRealMap_fderiv_bijective

end NLA.Proofs.SP14
