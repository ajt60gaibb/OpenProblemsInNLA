import NLA.Proofs.RA05.HyperplaneDefinitions
import Mathlib.Tactic

/-! All-dimensional, exact transfer from strong subspace coresets to arbitrary
weighted lp subspace embeddings. This is support only, not the RA05 Target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
namespace NLA.Proofs.RA05

private theorem unit_dot_self {d : ℕ} (x : Fin d → ℝ)
    (hx : ∑ j, x j ^ 2 = 1) : dotProduct x x = 1 := by
  simpa only [dotProduct, pow_two] using hx

private theorem unit_ne_zero {d : ℕ} (x : Fin d → ℝ)
    (hx : ∑ j, x j ^ 2 = 1) : x ≠ 0 := by
  intro hz
  simp [hz] at hx

private theorem unitHyperplane_kills {d : ℕ} (x : Fin d → ℝ)
    (hx : ∑ j, x j ^ 2 = 1) : (UnitHyperplane x).mulVec x = 0 := by
  ext i
  simp [UnitHyperplane, Matrix.mulVec, dotProduct, Matrix.sub_apply,
    sub_mul, Finset.sum_sub_distrib, Matrix.vecMulVec_apply, Matrix.one_apply, mul_assoc,
    ← Finset.mul_sum, ← pow_two, hx]

theorem unitHyperplane_projector {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∑ j, x j ^ 2 = 1) :
    NLA.Statements.RA05.Projector (d - 1) (UnitHyperplane x) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp [UnitHyperplane, Matrix.transpose_apply, Matrix.sub_apply,
      Matrix.vecMulVec_apply, Matrix.one_apply, eq_comm, mul_comm]
  · unfold UnitHyperplane
    rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.vecMulVec_mul_vecMulVec, unit_dot_self x hx,
      one_smul]
    abel
  · have hkill := unitHyperplane_kills x hx
    have hker : x ∈ LinearMap.ker (UnitHyperplane x).mulVecLin := by
      exact hkill
    have hkpos : 0 < Module.finrank ℝ (LinearMap.ker (UnitHyperplane x).mulVecLin) := by
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      refine ⟨⟨x, hker⟩, ?_⟩
      intro hz
      exact unit_ne_zero x hx (congrArg Subtype.val hz)
    have hdim := LinearMap.finrank_range_add_finrank_ker (UnitHyperplane x).mulVecLin
    have hdim' : (UnitHyperplane x).rank +
        Module.finrank ℝ (LinearMap.ker (UnitHyperplane x).mulVecLin) = d := by
      simpa only [Matrix.rank, Module.finrank_pi, Module.finrank_self,
        Fintype.card_fin, mul_one] using hdim
    omega

private theorem residual_unitHyperplane {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (x : Fin d → ℝ)
    (i : Fin n) (j : Fin d) :
    A i j - ∑ h, A i h * UnitHyperplane x h j =
      NLA.Statements.RA06.RowValue A i x * x j := by
  simp only [UnitHyperplane, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, NLA.Statements.RA06.RowValue]
  simp only [Finset.sum_mul, mul_assoc]
  ring

theorem rowCost_unitHyperplane {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p : ℝ)
    (x : Fin d → ℝ) (hx : ∑ j, x j ^ 2 = 1) (i : Fin n) :
    NLA.Statements.RA05.RowCost A p (UnitHyperplane x) i =
      Real.rpow |NLA.Statements.RA06.RowValue A i x| p := by
  unfold NLA.Statements.RA05.RowCost
  simp_rw [residual_unitHyperplane, mul_pow]
  rw [← Finset.mul_sum, hx, mul_one, Real.sqrt_sq_eq_abs]
  rfl

private theorem rowValue_scale {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (i : Fin n)
    (r : ℝ) (u : Fin d → ℝ) :
    NLA.Statements.RA06.RowValue A i (fun j => r * u j) =
      r * NLA.Statements.RA06.RowValue A i u := by
  simp only [NLA.Statements.RA06.RowValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem energy_scale {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p r : ℝ) (hr : 0 < r)
    (u : Fin d → ℝ) :
    NLA.Statements.RA06.InputEnergy A p (fun j => r * u j) =
      Real.rpow r p * NLA.Statements.RA06.InputEnergy A p u := by
  simp only [NLA.Statements.RA06.InputEnergy, rowValue_scale,
    abs_mul, abs_of_pos hr, Real.rpow_eq_pow]
  simp_rw [Real.mul_rpow hr.le (abs_nonneg _)]
  rw [Finset.mul_sum]

private theorem weightedEnergy_scale {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p r : ℝ) (hr : 0 < r)
    (w : Fin n → ℝ) (u : Fin d → ℝ) :
    WeightedInputEnergy A p w (fun j => r * u j) =
      Real.rpow r p * WeightedInputEnergy A p w u := by
  simp only [WeightedInputEnergy, rowValue_scale, abs_mul, abs_of_pos hr,
    Real.rpow_eq_pow]
  simp_rw [Real.mul_rpow hr.le (abs_nonneg _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every actual strong rank-(d-1) coreset preserves all-vector lp energy.
The conclusion retains the exact same weights, exponent and accuracy. -/
theorem strongCoreset_implies_allVectorEmbedding {n d : ℕ}
    (hd : 0 < d) (A : Matrix (Fin n) (Fin d) ℝ)
    (p ε : ℝ) (hp : 0 < p) (w : Fin n → ℝ)
    (hcore : NLA.Statements.RA05.StrongCoreset A p (d - 1) ε w) :
    ∀ x : Fin d → ℝ,
      (1 - ε) * NLA.Statements.RA06.InputEnergy A p x ≤
        WeightedInputEnergy A p w x ∧
      WeightedInputEnergy A p w x ≤
        (1 + ε) * NLA.Statements.RA06.InputEnergy A p x := by
  intro y
  by_cases hy : y = 0
  · subst y
    simp [NLA.Statements.RA06.InputEnergy, NLA.Statements.RA06.RowValue,
      WeightedInputEnergy, Real.zero_rpow hp.ne']
  have hSpos : 0 < ∑ j, y j ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
    apply Finset.sum_pos'
    · intro j _
      exact sq_nonneg _
    · exact ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero (by simpa using hj)⟩
  let r := Real.sqrt (∑ j, y j ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr hSpos
  have hrsq : r ^ 2 = ∑ j, y j ^ 2 := Real.sq_sqrt hSpos.le
  let u : Fin d → ℝ := fun j => y j / r
  have hu : ∑ j, u j ^ 2 = 1 := by
    simp only [u, div_pow, ← Finset.sum_div, ← hrsq]
    exact div_self (pow_ne_zero _ hr.ne')
  have hyu : y = fun j => r * u j := by
    funext j
    dsimp [u]
    field_simp
  have hbound := hcore.2 (UnitHyperplane u) (unitHyperplane_projector hd u hu)
  simp_rw [NLA.Statements.RA05.Cost, rowCost_unitHyperplane A p u hu] at hbound
  change (1 - ε) * NLA.Statements.RA06.InputEnergy A p u ≤
      WeightedInputEnergy A p w u ∧
    WeightedInputEnergy A p w u ≤
      (1 + ε) * NLA.Statements.RA06.InputEnergy A p u at hbound
  have hc : 0 ≤ Real.rpow r p := (Real.rpow_pos_of_pos hr p).le
  rw [hyu, energy_scale A p r hr u, weightedEnergy_scale A p r hr w u]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hbound.1 hc]
  · nlinarith [mul_le_mul_of_nonneg_left hbound.2 hc]

end NLA.Proofs.RA05
