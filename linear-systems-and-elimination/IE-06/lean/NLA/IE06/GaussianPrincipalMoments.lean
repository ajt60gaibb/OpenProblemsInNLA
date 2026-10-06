/-
Exact Gaussian inverse principal Gram moments. The unconditional repeated-row
integration route was independently approved before implementation in
reviews/gaussian-principal-moments-specification.md.
-/
import NLA.IE06.GaussianDeterminantMoments

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace NLA.IE06.GaussianPrincipalMoments
open GaussianNull GaussianQuadratic GaussianRegression GaussianDeterminantMoments
local instance gaussianRect_probability (m n : ℕ) : IsProbabilityMeasure (gaussianRect m n) := by
  unfold gaussianRect
  infer_instance

/-- Delete the first r rows; the total row dimension is written k+r so that
successive first-row integration has definitionally compatible dimensions. -/
def tailRows {k n : ℕ} (r : ℕ) (G : RectMat (k + r) n) : RectMat k n :=
  fun i => G ⟨r + i.val, by omega⟩

theorem tailRows_zero {k n : ℕ} (G : RectMat (k + 0) n) : tailRows 0 G = G := by
  ext i j
  simp [tailRows]

theorem tailRows_cons {k n r : ℕ} (B : RectMat (k + r) n) (y : Fin n → ℝ) :
    tailRows (r + 1) (Fin.cons y B) = tailRows r B := by
  ext i j
  have he : (⟨r + 1 + i.val, by omega⟩ : Fin (k + (r + 1))) =
      (⟨r + i.val, by omega⟩ : Fin (k + r)).succ := by ext; simp; omega
  simp only [tailRows, he, Fin.cons_succ]

def detRatio {k n : ℕ} (r : ℕ) (G : RectMat (k + r) n) : ℝ :=
  (gram (tailRows r G)).det / (gram G).det

theorem detRatio_nonneg {k n r : ℕ} (G : RectMat (k + r) n) : 0 ≤ detRatio r G := by
  apply div_nonneg
  · exact (Matrix.posSemidef_self_mul_conjTranspose (Matrix.of (tailRows r G))).det_nonneg
  · exact (Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)).det_nonneg

theorem detRatio_measurable (k n r : ℕ) : Measurable (@detRatio k n r) := by
  have hc : Continuous (@tailRows k n r) := by unfold tailRows; fun_prop
  exact (gram_continuous.comp hc).matrix_det.measurable.div gram_continuous.matrix_det.measurable

theorem detRatio_cons_factor {k n r : ℕ} (B : RectMat (k + r) n) (y : Fin n → ℝ)
    (hB : (gram B).det ≠ 0) (hG : (gram (Fin.cons y B)).det ≠ 0) (q : ℕ) :
    detRatio (r + 1) (Fin.cons y B) ^ q =
      detRatio r B ^ q * (‖residual B y‖ ^ (2 * q))⁻¹ := by
  simp only [detRatio, tailRows_cons]
  simp only [div_pow]
  simp only [div_eq_mul_inv]
  rw [inverse_det_cons_factor B y hB hG q]
  ring

/-- Exact ratio moment, with the complement rows still random under the
literal iid Gaussian law. This is sufficient for the principal-minor Markov step. -/
theorem gaussian_detRatio_moment (k r n q : ℕ) (hn : k + r + 2 * q ≤ n) :
    Integrable (fun G : RectMat (k + r) n => detRatio r G ^ q) (gaussianRect (k + r) n) ∧
    (∫ G : RectMat (k + r) n, detRatio r G ^ q ∂gaussianRect (k + r) n) =
      ∏ a ∈ Finset.range r, ∏ b ∈ Finset.range q, (((n - k - a : ℕ) : ℝ) - 2 * (b + 1))⁻¹ := by
  induction r with
  | zero =>
    have heq : (fun G : RectMat (k + 0) n => detRatio 0 G ^ q) =ᵐ[gaussianRect (k + 0) n]
        (fun _ => (1 : ℝ)) := by
      filter_upwards [gram_det_ne_zero_ae (k + 0) n (by omega)] with G hG
      simp [detRatio, tailRows_zero, hG]
    refine ⟨(integrable_const 1).congr heq.symm, ?_⟩
    rw [integral_congr_ae heq]
    simp
  | succ r ih =>
    obtain ⟨hBi, hBe⟩ := ih (by omega)
    let C : ℝ := (∏ b ∈ Finset.range q, (((n - (k + r) : ℕ) : ℝ) - 2 * (b + 1)))⁻¹
    let f : RectMat (k + (r + 1)) n → ℝ := fun G => detRatio (r + 1) G ^ q
    let b : RectMat (k + r) n → ℝ := fun B => detRatio r B ^ q
    let c : RectMat (k + r) n × (Fin n → ℝ) → RectMat (k + (r + 1)) n :=
      fun z => Fin.cons z.2 z.1
    have hmp : MeasurePreserving c ((gaussianRect (k + r) n).prod (gaussianVector n))
        (gaussianRect (k + (r + 1)) n) :=
      (gaussian_cons_measurePreserving (k + r) n).comp Measure.measurePreserving_swap
    have hfm : Measurable f := (detRatio_measurable k n (r + 1)).pow_const q
    have hcAE : ∀ᵐ z ∂(gaussianRect (k + r) n).prod (gaussianVector n),
        (gram (c z)).det ≠ 0 :=
      hmp.quasiMeasurePreserving.ae (gram_det_ne_zero_ae (k + (r + 1)) n (by omega))
    have hcond : ∀ᵐ B ∂gaussianRect (k + r) n,
        Integrable (fun y => f (c (B, y))) (gaussianVector n) ∧
        (∫ y, f (c (B, y)) ∂gaussianVector n) = b B * C ∧
        (∫ y, ‖f (c (B, y))‖ ∂gaussianVector n) = b B * C := by
      filter_upwards [gram_posDef_ae (k + r) n (by omega), Measure.ae_ae_of_ae_prod hcAE] with B hB hdet
      obtain ⟨hri, hre⟩ := residual_inverse_norm_moment B hB q (by omega)
      have heq : (fun y => f (c (B, y))) =ᵐ[gaussianVector n]
          (fun y => b B * (‖residual B y‖ ^ (2 * q))⁻¹) := by
        filter_upwards [hdet] with y hy
        exact detRatio_cons_factor B y (ne_of_gt hB.det_pos) hy q
      have hb : 0 ≤ b B := pow_nonneg (detRatio_nonneg B) q
      have hnq : (fun y => ‖f (c (B, y))‖) =ᵐ[gaussianVector n]
          (fun y => b B * (‖residual B y‖ ^ (2 * q))⁻¹) := by
        filter_upwards [heq] with y hy
        rw [hy, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb (by positivity))]
      refine ⟨(hri.const_mul (b B)).congr heq.symm, ?_, ?_⟩
      · rw [integral_congr_ae heq, integral_const_mul, hre]
      · rw [integral_congr_ae hnq, integral_const_mul, hre]
    have hfi : Integrable (f ∘ c) ((gaussianRect (k + r) n).prod (gaussianVector n)) := by
      apply (integrable_prod_iff (hfm.comp hmp.measurable).aestronglyMeasurable).mpr
      refine ⟨hcond.mono fun B hB => hB.1, ?_⟩
      exact (hBi.mul_const C).congr (hcond.mono fun B hB => hB.2.2.symm)
    refine ⟨(hmp.integrable_comp hfm.aestronglyMeasurable).mp hfi, ?_⟩
    change (∫ G, f G ∂gaussianRect (k + (r + 1)) n) = _
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hfm.aestronglyMeasurable]
    change (∫ z, (f ∘ c) z ∂(gaussianRect (k + r) n).prod (gaussianVector n)) = _
    rw [integral_prod _ hfi]
    simp only [Function.comp_apply]
    rw [integral_congr_ae (hcond.mono fun B hB => hB.2.1), integral_mul_const]
    change (∫ B, detRatio r B ^ q ∂gaussianRect (k + r) n) * C = _
    rw [hBe, Finset.prod_range_succ]
    congr 1
    simp only [C, Finset.prod_inv_distrib, Nat.sub_sub]

theorem det_inverse_upper_block {r k : ℕ}
    (T : Matrix (Fin r ⊕ Fin k) (Fin r ⊕ Fin k) ℝ) (hT : T.PosDef) :
    (T⁻¹.toBlocks₁₁).det = T.toBlocks₂₂.det / T.det := by
  let A := T.toBlocks₁₁
  let B := T.toBlocks₁₂
  let C := T.toBlocks₂₁
  let D := T.toBlocks₂₂
  have hD : D.PosDef := hT.submatrix Sum.inr_injective
  have hblocks : Matrix.fromBlocks A B C D = T := Matrix.fromBlocks_toBlocks T
  have hU : IsUnit (Matrix.fromBlocks A B C D) := hblocks ▸ hT.isUnit
  cases hD.isUnit.nonempty_invertible
  cases hU.nonempty_invertible
  let := Matrix.invertibleOfFromBlocks₂₂Invertible A B C D
  have hd : D.det ≠ 0 := ne_of_gt hD.det_pos
  rw [← hblocks]
  change ((Matrix.fromBlocks A B C D)⁻¹.toBlocks₁₁).det = D.det / (Matrix.fromBlocks A B C D).det
  rw [← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₂₂_eq,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Matrix.det_fromBlocks₂₂]
  rw [div_mul_eq_div_div, div_self hd, one_div]

def blockEquiv (k r : ℕ) : Fin r ⊕ Fin k ≃ Fin (k + r) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm r k))

def headIndex (k r : ℕ) (i : Fin r) : Fin (k + r) := blockEquiv k r (Sum.inl i)

theorem headIndex_val (k r : ℕ) (i : Fin r) : (headIndex k r i).val = i.val := rfl

def principalInverseDet {k n : ℕ} (r : ℕ) (G : RectMat (k + r) n) : ℝ :=
  ((gram G)⁻¹.submatrix (headIndex k r) (headIndex k r)).det

theorem principalInverseDet_eq_detRatio {k n r : ℕ} (G : RectMat (k + r) n)
    (hG : (gram G).PosDef) : principalInverseDet r G = detRatio r G := by
  let e := blockEquiv k r
  have h := det_inverse_upper_block ((gram G).submatrix e e) (hG.submatrix e.injective)
  have h11 : ((gram G).submatrix e e)⁻¹.toBlocks₁₁ =
      (gram G)⁻¹.submatrix (headIndex k r) (headIndex k r) := by
    rw [Matrix.inv_submatrix_equiv]
    rfl
  have h22 : ((gram G).submatrix e e).toBlocks₂₂ = gram (tailRows r G) := by
    ext i j
    rfl
  rw [h11, h22, Matrix.det_submatrix_equiv_self] at h
  exact h

theorem gaussian_principal_inverse_det_moment (k r n q : ℕ) (hn : k + r + 2 * q ≤ n) :
    Integrable (fun G : RectMat (k + r) n => principalInverseDet r G ^ q)
      (gaussianRect (k + r) n) ∧
    (∫ G : RectMat (k + r) n, principalInverseDet r G ^ q ∂gaussianRect (k + r) n) =
      ∏ a ∈ Finset.range r, ∏ b ∈ Finset.range q, (((n - k - a : ℕ) : ℝ) - 2 * (b + 1))⁻¹ := by
  obtain ⟨hi, he⟩ := gaussian_detRatio_moment k r n q hn
  have heq : (fun G : RectMat (k + r) n => principalInverseDet r G ^ q) =ᵐ[gaussianRect (k + r) n]
      (fun G => detRatio r G ^ q) := by
    filter_upwards [gram_posDef_ae (k + r) n (by omega)] with G hG
    rw [principalInverseDet_eq_detRatio G hG]
  exact ⟨hi.congr heq.symm, (integral_congr_ae heq).trans he⟩

def rowPermute {m n : ℕ} (σ : Equiv.Perm (Fin m)) (G : RectMat m n) : RectMat m n :=
  fun i => G (σ i)

theorem rowPermute_measurePreserving {m n : ℕ} (σ : Equiv.Perm (Fin m)) :
    MeasurePreserving (@rowPermute m n σ) (gaussianRect m n) (gaussianRect m n) := by
  convert measurePreserving_piCongrLeft (fun _ : Fin m => gaussianVector n) σ.symm using 1
  · funext G i
    simp [rowPermute, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  · rfl
  · rfl

theorem gram_rowPermute {m n : ℕ} (σ : Equiv.Perm (Fin m)) (G : RectMat m n) :
    gram (rowPermute σ G) = (gram G).submatrix σ σ := by
  ext i j
  rfl

/-- Any fixed injectively indexed principal submatrix has the same exact
moment. The row permutation acts on the actual iid Gaussian matrix law. -/
theorem gaussian_principal_submatrix_moment {k r n q : ℕ}
    (f : Fin r → Fin (k + r)) (hf : Function.Injective f) (hn : k + r + 2 * q ≤ n) :
    Integrable (fun G : RectMat (k + r) n => ((gram G)⁻¹.submatrix f f).det ^ q)
      (gaussianRect (k + r) n) ∧
    (∫ G : RectMat (k + r) n, ((gram G)⁻¹.submatrix f f).det ^ q ∂gaussianRect (k + r) n) =
      ∏ a ∈ Finset.range r, ∏ b ∈ Finset.range q, (((n - k - a : ℕ) : ℝ) - 2 * (b + 1))⁻¹ := by
  have hh : Function.Injective (headIndex k r) := (blockEquiv k r).injective.comp Sum.inl_injective
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (headIndex k r) f hh hf
  have heq (G : RectMat (k + r) n) :
      principalInverseDet r (rowPermute σ G) = ((gram G)⁻¹.submatrix f f).det := by
    simp only [principalInverseDet, gram_rowPermute, Matrix.inv_submatrix_equiv,
      Matrix.submatrix_submatrix, Function.comp_def, hσ]
  obtain ⟨hi, he⟩ := gaussian_principal_inverse_det_moment k r n q hn
  have hmp := rowPermute_measurePreserving (n := n) σ
  have hfun : (fun G : RectMat (k + r) n => ((gram G)⁻¹.submatrix f f).det ^ q) =
      (fun G => principalInverseDet r G ^ q) ∘ rowPermute σ := by
    funext G
    rw [Function.comp_apply, heq]
  rw [hfun]
  refine ⟨hmp.integrable_comp_of_integrable hi, ?_⟩
  have hm : AEStronglyMeasurable (fun G : RectMat (k + r) n => principalInverseDet r G ^ q)
      ((gaussianRect (k + r) n).map (rowPermute σ)) := by
    simpa only [hmp.map_eq] using hi.aestronglyMeasurable
  have hmap := integral_map hmp.measurable.aemeasurable hm
  simpa only [Function.comp_def, hmp.map_eq, he] using hmap.symm

theorem gaussian_principal_submatrix_moment_of_le {m r n q : ℕ}
    (f : Fin r → Fin m) (hf : Function.Injective f) (hrm : r ≤ m) (hn : m + 2 * q ≤ n) :
    Integrable (fun G : RectMat m n => ((gram G)⁻¹.submatrix f f).det ^ q) (gaussianRect m n) ∧
    (∫ G : RectMat m n, ((gram G)⁻¹.submatrix f f).det ^ q ∂gaussianRect m n) =
      ∏ a ∈ Finset.range r, ∏ b ∈ Finset.range q, (((n - (m - r) - a : ℕ) : ℝ) - 2 * (b + 1))⁻¹ := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hrm
  have hmk : m = k + r := by omega
  clear hk
  subst m
  simpa only [Nat.add_sub_cancel_right] using
    gaussian_principal_submatrix_moment (k := k) (r := r) f hf hn

/-- Exact moment for a literal finite principal subset, in the same subtype
coordinates as the characteristic-polynomial principal-minor expansion. -/
theorem gaussian_principal_subset_moment {m n q : ℕ} (S : Finset (Fin m)) (hn : m + 2 * q ≤ n) :
    Integrable (fun G : RectMat m n =>
      ((gram G)⁻¹.submatrix (Subtype.val : S → Fin m) Subtype.val).det ^ q) (gaussianRect m n) ∧
    (∫ G : RectMat m n, ((gram G)⁻¹.submatrix (Subtype.val : S → Fin m) Subtype.val).det ^ q
      ∂gaussianRect m n) =
      ∏ a ∈ Finset.range S.card, ∏ b ∈ Finset.range q,
        (((n - (m - S.card) - a : ℕ) : ℝ) - 2 * (b + 1))⁻¹ := by
  let e : Fin S.card ≃ S := S.equivFin.symm
  let f : Fin S.card → Fin m := fun i => (e i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hrm : S.card ≤ m := by simpa using S.card_le_univ
  have heq (G : RectMat m n) : ((gram G)⁻¹.submatrix f f).det =
      ((gram G)⁻¹.submatrix (Subtype.val : S → Fin m) Subtype.val).det := by
    simpa only [Matrix.submatrix_submatrix, Function.comp_def, f] using
      Matrix.det_submatrix_equiv_self e
        ((gram G)⁻¹.submatrix (Subtype.val : S → Fin m) Subtype.val)
  simpa only [heq] using gaussian_principal_submatrix_moment_of_le f hf hrm hn

#assert_trust kernel tailRows
#assert_trust kernel tailRows_zero
#assert_trust kernel tailRows_cons
#assert_trust kernel detRatio
#assert_trust kernel detRatio_nonneg
#assert_trust kernel detRatio_measurable
#assert_trust kernel detRatio_cons_factor
#assert_trust kernel gaussian_detRatio_moment
#assert_trust kernel det_inverse_upper_block
#assert_trust kernel blockEquiv
#assert_trust kernel headIndex
#assert_trust kernel headIndex_val
#assert_trust kernel principalInverseDet
#assert_trust kernel principalInverseDet_eq_detRatio
#assert_trust kernel gaussian_principal_inverse_det_moment
#assert_trust kernel rowPermute
#assert_trust kernel rowPermute_measurePreserving
#assert_trust kernel gram_rowPermute
#assert_trust kernel gaussian_principal_submatrix_moment
#assert_trust kernel gaussian_principal_submatrix_moment_of_le
#assert_trust kernel gaussian_principal_subset_moment
#print axioms gaussian_detRatio_moment
#print axioms gaussian_principal_inverse_det_moment
#print axioms gaussian_principal_submatrix_moment
#print axioms gaussian_principal_subset_moment
end NLA.IE06.GaussianPrincipalMoments
