import Mathlib
import LeanCert.Tactic.Verification
import NLA.Proofs.MF03.CosineAllComplexProduct

/-! Elementary-symmetric coefficient transfer for the MF-03 cosine product. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Real Topology
open Filter

namespace NLA.Proofs.MF03

noncomputable def cosineElementaryCoeff (j : ℕ) : ℝ :=
  tsum (fun s : {S : Finset ℕ // S.card = j} =>
    ∏ k ∈ s.1, cosineFactor (k + 1))

private theorem cosineFactor_pos (k : ℕ) : 0 < cosineFactor (k + 1) := by
  unfold cosineFactor
  have hk : (0 : ℝ) < (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
    have hnonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast
    linarith
  positivity

private theorem cosineCoefficients_summable :
    Summable (fun k : ℕ => cosineFactor (k + 1)) := by
  have hbase : Summable (fun k : ℕ =>
      1 / |(k : ℝ) + 1 / 2| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow (1 / 2) 2).2 (by norm_num)
  have hbase' : Summable (fun k : ℕ =>
      1 / |(k : ℝ) + 1 / 2| ^ (2 : ℕ)) := by
    simpa only [Real.rpow_two] using hbase
  have hscale := hbase'.mul_left (1 / Real.pi ^ 2)
  apply hscale.congr
  intro k
  have hcast : (((k + 1 : ℕ) : ℝ) - 1 / 2) = (k : ℝ) + 1 / 2 := by
    push_cast
    ring
  have hpos : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
  have hfactor : cosineFactor (k + 1) =
      1 / (Real.pi ^ 2 * ((k : ℝ) + 1 / 2) ^ 2) := by
    unfold cosineFactor
    rw [hcast]
  rw [hfactor, abs_of_pos hpos, one_div_mul_one_div]

private theorem cosineFinsetWeights_summable :
    Summable (fun S : Finset ℕ => ∏ k ∈ S, cosineFactor (k + 1)) := by
  apply summable_finsetProd_of_summable_norm
  simpa [Real.norm_eq_abs, abs_of_pos, cosineFactor_pos] using
    cosineCoefficients_summable

private theorem cosineFinsetWeights_nonneg (S : Finset ℕ) :
    0 ≤ ∏ k ∈ S, cosineFactor (k + 1) := by
  exact Finset.prod_nonneg (fun k hk => (cosineFactor_pos k).le)

private theorem cosineElementaryCoeff_summable :
    Summable cosineElementaryCoeff := by
  have hpartition := (summable_partition
      (f := fun S : Finset ℕ => ∏ k ∈ S, cosineFactor (k + 1))
      (s := fun j : ℕ => {S : Finset ℕ | S.card = j})
      cosineFinsetWeights_nonneg
      (by
        intro S
        refine ⟨S.card, rfl, ?_⟩
        intro j hj
        exact hj.symm)).mp cosineFinsetWeights_summable
  change Summable (fun j : ℕ =>
    tsum (fun s : {S : Finset ℕ // S.card = j} =>
      ∏ k ∈ s.1, cosineFactor (k + 1)))
  exact hpartition.2

private theorem cosineElementaryCoeff_fiber_summable (j : ℕ) :
    Summable (fun s : {S : Finset ℕ // S.card = j} =>
      ∏ k ∈ s.1, cosineFactor (k + 1)) := by
  have hpartition := (summable_partition
      (f := fun S : Finset ℕ => ∏ k ∈ S, cosineFactor (k + 1))
      (s := fun j : ℕ => {S : Finset ℕ | S.card = j})
      cosineFinsetWeights_nonneg
      (by
        intro S
        refine ⟨S.card, rfl, ?_⟩
        intro i hi
        exact hi.symm)).mp cosineFinsetWeights_summable
  exact hpartition.1 j

private theorem cosineElementaryCoeff_nonneg (j : ℕ) :
    0 ≤ cosineElementaryCoeff j := by
  unfold cosineElementaryCoeff
  exact tsum_nonneg (fun s => cosineFinsetWeights_nonneg s.1)

private def finsetCardEquiv : Finset ℕ ≃
    Σ j : ℕ, {S : Finset ℕ // S.card = j} where
  toFun S := ⟨S.card, ⟨S, rfl⟩⟩
  invFun p := p.2.1
  left_inv S := rfl
  right_inv := by
    rintro ⟨j, ⟨S, hS⟩⟩
    subst j
    rfl

private theorem cosineComplexFinsetWeights_summable (z : ℂ) :
    Summable (fun S : Finset ℕ =>
      ∏ k ∈ S, (cosineFactor (k + 1) : ℂ) * z) := by
  apply summable_finsetProd_of_summable_norm
  have h := cosineCoefficients_summable.mul_left ‖z‖
  apply h.congr
  intro k
  have ha := (cosineFactor_pos k).le
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, mul_comm]

private theorem cosineComplexFiber_eq (j : ℕ) (z : ℂ) :
    tsum (fun s : {S : Finset ℕ // S.card = j} =>
      ∏ k ∈ s.1, (cosineFactor (k + 1) : ℂ) * z) =
      (cosineElementaryCoeff j : ℂ) * z ^ j := by
  have hprod (s : {S : Finset ℕ // S.card = j}) :
      (∏ k ∈ s.1, (cosineFactor (k + 1) : ℂ) * z) =
        ((∏ k ∈ s.1, cosineFactor (k + 1) : ℝ) : ℂ) * z ^ j := by
    rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod]
    simp [Finset.prod_const, s.2]
  calc
    tsum (fun s : {S : Finset ℕ // S.card = j} =>
        ∏ k ∈ s.1, (cosineFactor (k + 1) : ℂ) * z) =
        tsum (fun s : {S : Finset ℕ // S.card = j} =>
          ((∏ k ∈ s.1, cosineFactor (k + 1) : ℝ) : ℂ) * z ^ j) := by
      apply tsum_congr
      intro s
      exact hprod s
    _ = (tsum (fun s : {S : Finset ℕ // S.card = j} =>
          ((∏ k ∈ s.1, cosineFactor (k + 1) : ℝ) : ℂ))) * z ^ j := by
      rw [tsum_mul_right]
    _ = (cosineElementaryCoeff j : ℂ) * z ^ j := by
      rw [← Complex.ofReal_tsum]
      rfl

/-- The absolutely convergent cosine product expands by finite-subset cardinality. -/
theorem cosineProduct_eq_elementarySeries (z : ℂ) :
    tprod (fun k : ℕ =>
      (1 : ℂ) + (cosineFactor (k + 1) : ℂ) * z) =
      tsum (fun j : ℕ => (cosineElementaryCoeff j : ℂ) * z ^ j) := by
  let F : Finset ℕ → ℂ := fun S =>
    ∏ k ∈ S, (cosineFactor (k + 1) : ℂ) * z
  have hF : Summable F := cosineComplexFinsetWeights_summable z
  have hσ : Summable (fun p : Σ j : ℕ, {S : Finset ℕ // S.card = j} =>
      F p.2.1) := by
    change Summable (F ∘ finsetCardEquiv.symm)
    exact finsetCardEquiv.symm.summable_iff.mpr hF
  have hσfiber (j : ℕ) : Summable
      (fun s : {S : Finset ℕ // S.card = j} => F s.1) :=
    hσ.sigma_factor j
  calc
    tprod (fun k : ℕ =>
        (1 : ℂ) + (cosineFactor (k + 1) : ℂ) * z) =
        tsum F := by
      exact tprod_one_add hF
    _ = tsum (fun p : Σ j : ℕ, {S : Finset ℕ // S.card = j} =>
        F p.2.1) := by
      exact (finsetCardEquiv.symm.tsum_eq F).symm
    _ = tsum (fun j : ℕ =>
        tsum (fun s : {S : Finset ℕ // S.card = j} => F s.1)) := by
      exact Summable.tsum_sigma' hσfiber hσ
    _ = tsum (fun j : ℕ => (cosineElementaryCoeff j : ℂ) * z ^ j) := by
      apply tsum_congr
      intro j
      exact cosineComplexFiber_eq j z

private theorem factorialEven_summable :
    Summable (fun j : ℕ => (1 : ℝ) / ((2 * j).factorial : ℝ)) := by
  have hbase : Summable (fun j : ℕ => (1 : ℝ) / (j.factorial : ℝ)) := by
    simpa using Real.summable_pow_div_factorial 1
  apply Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hbase
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.factorial_le (by omega : j ≤ 2 * j)

private noncomputable def elementarySeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun j => (cosineElementaryCoeff j : ℂ))

private noncomputable def factorialSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun j => (1 : ℂ) / ((2 * j).factorial : ℂ))

private theorem elementarySeries_radius_pos : 0 < elementarySeries.radius := by
  have hs : Summable (fun j => ‖elementarySeries j‖ * (1 : ℝ) ^ j) := by
    convert cosineElementaryCoeff_summable using 1
    ext j
    simp [elementarySeries, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cosineElementaryCoeff_nonneg j)]
  have hr : (1 : ENNReal) ≤ elementarySeries.radius := by
    simpa using (elementarySeries.le_radius_of_summable_norm (r := 1) hs)
  exact (by norm_num : (0 : ENNReal) < 1).trans_le hr

private theorem factorialSeries_radius_pos : 0 < factorialSeries.radius := by
  have hs : Summable (fun j => ‖factorialSeries j‖ * (1 : ℝ) ^ j) := by
    convert factorialEven_summable using 1
    ext j
    simp [factorialSeries]
  have hr : (1 : ENNReal) ≤ factorialSeries.radius := by
    simpa using (factorialSeries.le_radius_of_summable_norm (r := 1) hs)
  exact (by norm_num : (0 : ENNReal) < 1).trans_le hr

private theorem elementarySeries_sum_eq_waveSeries : elementarySeries.sum = waveSeries := by
  funext z
  calc
    elementarySeries.sum z =
        tsum (fun j : ℕ => (cosineElementaryCoeff j : ℂ) * z ^ j) := by
      exact FormalMultilinearSeries.ofScalars_sum_eq _ z
    _ = tprod (fun k : ℕ =>
        (1 : ℂ) + (cosineFactor (k + 1) : ℂ) * z) :=
      (cosineProduct_eq_elementarySeries z).symm
    _ = waveSeries z := cosineFactor_tprod_eq_waveSeries z

private theorem factorialSeries_sum_eq_waveSeries : factorialSeries.sum = waveSeries := by
  funext z
  calc
    factorialSeries.sum z =
        tsum (fun j : ℕ => ((1 : ℂ) / ((2 * j).factorial : ℂ)) * z ^ j) := by
      exact FormalMultilinearSeries.ofScalars_sum_eq _ z
    _ = waveSeries z := by
      unfold waveSeries
      congr 1
      funext j
      ring

/-- The elementary symmetric coefficient is the exact factorial wave coefficient. -/
theorem cosineElementaryCoeff_eq_factorial (j : ℕ) :
    cosineElementaryCoeff j =
      (1 : ℝ) / ((2 * j).factorial : ℝ) := by
  have hp : HasFPowerSeriesAt waveSeries elementarySeries 0 :=
    elementarySeries_sum_eq_waveSeries ▸
      (elementarySeries.hasFPowerSeriesOnBall elementarySeries_radius_pos).hasFPowerSeriesAt
  have hq : HasFPowerSeriesAt waveSeries factorialSeries 0 :=
    factorialSeries_sum_eq_waveSeries ▸
      (factorialSeries.hasFPowerSeriesOnBall factorialSeries_radius_pos).hasFPowerSeriesAt
  have heq : elementarySeries = factorialSeries := hp.eq_formalMultilinearSeries hq
  have hcoeff := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ =>
    p.coeff j) heq
  have hc : (cosineElementaryCoeff j : ℂ) =
      (1 : ℂ) / ((2 * j).factorial : ℂ) := by
    simpa [elementarySeries, factorialSeries] using hcoeff
  exact Complex.ofReal_injective (by simpa using hc)

#assert_trust kernel cosineProduct_eq_elementarySeries
#assert_trust kernel cosineElementaryCoeff_eq_factorial
#print axioms cosineProduct_eq_elementarySeries
#print axioms cosineElementaryCoeff_eq_factorial

end NLA.Proofs.MF03
