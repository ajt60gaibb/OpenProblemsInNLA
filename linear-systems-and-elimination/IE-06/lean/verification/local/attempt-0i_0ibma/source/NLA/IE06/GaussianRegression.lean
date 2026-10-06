/-
Gaussian regression inverse-moment work. The exact preimplementation contract
is recorded in reviews/gaussian-regression-specification.md.
The product-law transpose and inverse measurability proofs adapt supporting
structure from the user's local AI-assisted RRF formalization; exact source
identities are in source/gaussian-regression-provenance.json. No RRF import.
-/
import NLA.IE06.GaussianSmallest

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace NLA.IE06.GaussianRegression
open GaussianNull GaussianQuadratic
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
local instance matrixBorelSpace (d : ℕ) : BorelSpace (Mat d) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
local instance gaussianRect_probability (m n : ℕ) : IsProbabilityMeasure (gaussianRect m n) := by
  unfold gaussianRect
  infer_instance

def gram {m n : ℕ} (G : RectMat m n) : Mat m := Matrix.of G * (Matrix.of G)ᴴ

/-- This is the ordinary inverse quadratic form, totalized to zero on singular
Gram matrices. Its full-rank almost-everywhere interpretation is proved below. -/
def directionalQuadratic {m n : ℕ} (G : RectMat m n) (v : E m) : ℝ :=
  ofLp v ⬝ᵥ (gram G)⁻¹ *ᵥ ofLp v

theorem measurable_inverse (m : ℕ) : Measurable (fun A : Mat m => A⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

theorem gram_continuous {m n : ℕ} : Continuous (@gram m n) := by
  unfold gram
  fun_prop

theorem directionalQuadratic_measurable {m n : ℕ} (v : E m) :
    Measurable (fun G : RectMat m n => directionalQuadratic G v) := by
  have hi := (measurable_inverse m).comp (gram_continuous (m := m) (n := n)).measurable
  unfold directionalQuadratic Matrix.mulVec dotProduct
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
    (Finset.measurable_sum _ (fun j _ => ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp hi)).mul measurable_const)))

theorem gaussian_uncurry (m n : ℕ) :
    (gaussianRect m n).map Function.uncurry =
      Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have heq : Function.uncurry ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i : Fin m => Set.pi Set.univ (fun j : Fin n => s (i, j))) := by
    ext G
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h i j => h (i, j), fun h ij => h ij.1 ij.2⟩
  rw [heq]
  simp only [gaussianRect, Measure.pi_pi, Fintype.prod_prod_type]

def transpose {m n : ℕ} (G : RectMat m n) : RectMat n m := fun j i => G i j

theorem gaussian_transpose (m n : ℕ) :
    (gaussianRect m n).map transpose = gaussianRect n m := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin m => ℝ)
    (Equiv.prodComm (Fin m) (Fin n))
  have hmap : Measure.map e (Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1)) =
      Measure.pi (fun _ : Fin n × Fin m => gaussianReal 0 1) :=
    (measurePreserving_piCongrLeft (fun _ : Fin n × Fin m => gaussianReal 0 1)
      (Equiv.prodComm (Fin m) (Fin n))).map_eq
  apply (MeasurableEquiv.curry (Fin n) (Fin m) ℝ).symm.measurableEmbedding.map_injective
  change Measure.map Function.uncurry (Measure.map transpose (gaussianRect m n)) =
    Measure.map Function.uncurry (gaussianRect n m)
  rw [Measure.map_map (by fun_prop) (by unfold transpose; fun_prop), gaussian_uncurry]
  have hf : Function.uncurry ∘ (@transpose m n) = e ∘ Function.uncurry := rfl
  rw [hf, ← Measure.map_map e.measurable (by fun_prop), gaussian_uncurry, hmap]

def coordinateIsometry {d : ℕ} (f : E d ≃ₗᵢ[ℝ] E d) (z : Fin d → ℝ) : Fin d → ℝ :=
  ofLp (f (toLp 2 z))

theorem coordinateIsometry_measurable {d : ℕ} (f : E d ≃ₗᵢ[ℝ] E d) :
    Measurable (coordinateIsometry f) := by
  unfold coordinateIsometry
  fun_prop

theorem gaussian_coordinateIsometry {d : ℕ} (f : E d ≃ₗᵢ[ℝ] E d) :
    (gaussianVector d).map (coordinateIsometry f) = gaussianVector d := by
  have h := stdGaussian_map f
  rw [← map_pi_eq_stdGaussian] at h
  have hh := congrArg (fun μ : Measure (E d) => μ.map ofLp) h
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hh
  change (gaussianVector d).map (fun z => ofLp (f (toLp 2 z))) = gaussianVector d
  simpa [Function.comp_def, gaussianVector] using hh

/-- The Gram matrix is positive definite almost surely for a wide Gaussian
matrix. No square Gaussian matrix is substituted for the rectangular law. -/
theorem gram_posDef_ae (m n : ℕ) (hmn : m ≤ n) :
    ∀ᵐ G ∂gaussianRect m n, (gram G).PosDef := by
  have hminor := gaussian_minor_det_ne_zero n m hmn
  rw [← gaussian_transpose m n] at hminor
  have hp := ae_of_ae_map (show Measurable (@transpose m n) by unfold transpose; fun_prop).aemeasurable hminor
  filter_upwards [hp] with G hG
  let C : Mat m := fun i j => G i (Fin.castLE hmn j)
  have hC : C.det ≠ 0 := by
    change Cᵀ.det ≠ 0 at hG
    simpa only [Matrix.det_transpose] using hG
  have hinj : Function.Injective (Matrix.of G).vecMul := by
    intro x y hxy
    have he : x ᵥ* C = y ᵥ* C := by
      funext j
      exact congrFun hxy (Fin.castLE hmn j)
    exact (Matrix.vecMul_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC))) he
  exact Matrix.PosDef.mul_conjTranspose_self (Matrix.of G) hinj

theorem gram_det_ne_zero_ae (m n : ℕ) (hmn : m ≤ n) :
    ∀ᵐ G ∂gaussianRect m n, (gram G).det ≠ 0 := by
  filter_upwards [gram_posDef_ae m n hmn] with G hG
  exact hG.det_pos.ne'

/-- Apply the same fixed Euclidean isometry independently to every row. -/
def rotateRows {m n : ℕ} (f : E n ≃ₗᵢ[ℝ] E n) (G : RectMat m n) : RectMat m n :=
  fun i => coordinateIsometry f (G i)

theorem rotateRows_measurePreserving {m n : ℕ} (f : E n ≃ₗᵢ[ℝ] E n) :
    MeasurePreserving (rotateRows (m := m) f) (gaussianRect m n) (gaussianRect m n) := by
  exact measurePreserving_pi (fun _ : Fin m => gaussianVector n) (fun _ : Fin m => gaussianVector n)
    (fun _ => ⟨coordinateIsometry_measurable f, gaussian_coordinateIsometry f⟩)

/-- Fixed Euclidean row-coordinate rotations of all columns preserve the
actual nested iid law, by the proved transpose law and rowwise invariance. -/
def rotateColumns {m n : ℕ} (f : E m ≃ₗᵢ[ℝ] E m) (G : RectMat m n) : RectMat m n :=
  transpose (rotateRows f (transpose G))

theorem rotateColumns_measurePreserving {m n : ℕ} (f : E m ≃ₗᵢ[ℝ] E m) :
    MeasurePreserving (rotateColumns (n := n) f) (gaussianRect m n) (gaussianRect m n) := by
  have ht (a b : ℕ) : MeasurePreserving (@transpose a b) (gaussianRect a b) (gaussianRect b a) :=
    ⟨by unfold transpose; fun_prop, gaussian_transpose a b⟩
  exact (ht n m).comp ((rotateRows_measurePreserving f).comp (ht m n))

/-- The Euclidean span of the fixed remaining rows. -/
def rowSpan {s n : ℕ} (B : RectMat s n) : Submodule ℝ (E n) :=
  Submodule.span ℝ (Set.range fun i => toLp 2 (B i))

def residual {s n : ℕ} (B : RectMat s n) (y : Fin n → ℝ) : E n :=
  (rowSpan B)ᗮ.starProjection (toLp 2 y)

/-- Exact deterministic inverse-Gram/orthogonal-residual identity. The sole
nondegeneracy premise concerns the full augmented Gram matrix. -/
theorem inverse_gram_first_diagonal {s n : ℕ} (B : RectMat s n) (y : Fin n → ℝ)
    (hG : (gram (Fin.cons y B)).det ≠ 0) :
    (gram (Fin.cons y B))⁻¹ 0 0 = (‖residual B y‖ ^ 2)⁻¹ := by
  let G : RectMat (s + 1) n := Fin.cons y B
  let c : Fin (s + 1) → ℝ := fun j => (gram G)⁻¹ j 0
  let u : E n := ∑ j, c j • toLp 2 (G j)
  have hprod : gram G * (gram G)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG)
  have hrow (i : Fin (s + 1)) : ⟪toLp 2 (G i), u⟫ = if i = 0 then 1 else 0 := by
    have hp := congrArg (fun A : Mat (s + 1) => A i 0) hprod
    rw [Matrix.one_apply] at hp
    convert hp using 1
    simp only [u, inner_sum, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, dotProduct, gram, Matrix.mul_apply, Matrix.conjTranspose_apply,
      star_trivial, Matrix.of_apply, c, Finset.sum_mul, ofLp_smul, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hu : u ∈ (rowSpan B)ᗮ := by
    rw [rowSpan, Submodule.mem_orthogonal']
    intro v hv
    apply Submodule.span_induction (p := fun v _ => ⟪u, v⟫ = 0) ?_ ?_ ?_ ?_ hv
    · rintro v ⟨i, rfl⟩
      have h := hrow i.succ
      simpa only [G, Fin.cons_succ, Fin.succ_ne_zero, if_false, real_inner_comm] using h
    · simp
    · intro a b ha hb haa hbb
      simp [inner_add_right, haa, hbb]
    · intro a v hv hh
      simp [real_inner_smul_right, hh]
  have hBu (j : Fin s) : (rowSpan B)ᗮ.starProjection (toLp 2 (B j)) = 0 := by
    apply (Submodule.starProjection_apply_eq_zero_iff (K := (rowSpan B)ᗮ)).mpr
    apply (rowSpan B).le_orthogonal_orthogonal
    exact Submodule.subset_span (Set.mem_range_self j)
  have hup : u = c 0 • residual B y := by
    have hh := Submodule.starProjection_eq_self_iff.mpr hu
    change (rowSpan B)ᗮ.starProjection (∑ j, c j • toLp 2 (G j)) = u at hh
    rw [map_sum, Fin.sum_univ_succ] at hh
    simp only [map_smul, G, Fin.cons_zero, Fin.cons_succ, hBu, smul_zero,
      Finset.sum_const_zero, add_zero] at hh
    exact hh.symm
  have hinner : ⟪toLp 2 y, residual B y⟫ = ‖residual B y‖ ^ 2 := by
    have hh := (rowSpan B)ᗮ.starProjection_inner_eq_zero (toLp 2 y) (residual B y)
      (Submodule.starProjection_apply_mem _ _)
    change ⟪toLp 2 y - residual B y, residual B y⟫ = 0 at hh
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at hh
    linarith
  have he := hrow 0
  rw [hup] at he
  simp only [G, Fin.cons_zero, ite_true, real_inner_smul_right, hinner] at he
  have hn : ‖residual B y‖ ^ 2 ≠ 0 := by intro hz; rw [hz, mul_zero] at he; norm_num at he
  have hh : c 0 = 1 / (‖residual B y‖ ^ 2) := (eq_div_iff hn).mpr he
  simpa only [one_div, c, G] using hh

/-- Orthogonal projection of a standard Gaussian is standard Gaussian on the
subspace, with its induced Euclidean structure. -/
theorem stdGaussian_projection {n : ℕ} (K : Submodule ℝ (E n)) :
    (stdGaussian (E n)).map K.orthogonalProjectionOnto = stdGaussian K := by
  apply Measure.ext_of_charFun
  ext t
  have heq : charFun ((stdGaussian (E n)).map K.orthogonalProjectionOnto) t =
      charFun (stdGaussian (E n)) (t : E n) := by
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), charFun_apply]
    apply integral_congr_ae
    filter_upwards [] with z
    congr 3
    exact K.inner_orthogonalProjectionOnto_eq_of_mem_right t z
  rw [heq, charFun_stdGaussian, charFun_stdGaussian]
  rfl

/-- Exact inverse moments of a fixed-subspace Gaussian projection. The basis
used to identify the subspace is deterministic, not a random measurable choice. -/
theorem projected_inverse_norm_moment {n : ℕ} (K : Submodule ℝ (E n)) (q : ℕ)
    (hdq : 2 * q < Module.finrank ℝ K) :
    Integrable (fun z : E n => (‖K.starProjection z‖ ^ (2 * q))⁻¹) (stdGaussian (E n)) ∧
      (∫ z : E n, (‖K.starProjection z‖ ^ (2 * q))⁻¹ ∂stdGaussian (E n)) =
        (∏ j ∈ Finset.range q, ((Module.finrank ℝ K : ℝ) - 2 * (j + 1)))⁻¹ := by
  let b := stdOrthonormalBasis ℝ K
  have hp : MeasurePreserving K.orthogonalProjectionOnto (stdGaussian (E n)) (stdGaussian K) :=
    ⟨by fun_prop, stdGaussian_projection K⟩
  have hb : MeasurePreserving b.repr (stdGaussian K)
      (stdGaussian (E (Module.finrank ℝ K))) := ⟨by fun_prop, stdGaussian_map b.repr⟩
  have hmp := hb.comp hp
  obtain ⟨hi, he⟩ := GaussianSmallest.gaussian_inverse_norm_moment (Module.finrank ℝ K) q hdq
  have hnorm (z : E n) : ‖b.repr (K.orthogonalProjectionOnto z)‖ = ‖K.starProjection z‖ := by
    rw [b.repr.norm_map]
    rfl
  constructor
  · simpa only [Function.comp_def, hnorm] using hmp.integrable_comp_of_integrable hi
  · rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by fun_prop)] at he
    simpa only [Function.comp_def, hnorm] using he

theorem rowSpan_finrank {s n : ℕ} (B : RectMat s n) (hB : (gram B).PosDef) :
    Module.finrank ℝ (rowSpan B) = s := by
  have hinj : Function.Injective (Matrix.of B).vecMul := by
    intro x y hxy
    apply Matrix.vecMul_injective_of_isUnit hB.isUnit
    have hh := congrArg (fun z => z ᵥ* (Matrix.of B)ᴴ) hxy
    simpa only [Matrix.vecMul_vecMul, gram] using hh
  have hlin := Matrix.vecMul_injective_iff.mp hinj
  have he := hlin.map' (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.injective)
  change LinearIndependent ℝ (fun i => toLp 2 (B i)) at he
  simpa only [rowSpan, Fintype.card_fin] using finrank_span_eq_card he

theorem rowSpan_orthogonal_finrank {s n : ℕ} (B : RectMat s n) (hB : (gram B).PosDef) :
    Module.finrank ℝ (rowSpan B)ᗮ = n - s := by
  have h := (rowSpan B).finrank_add_finrank_orthogonal
  rw [rowSpan_finrank B hB] at h
  simp only [E, finrank_euclideanSpace, Fintype.card_fin] at h
  simpa only [Nat.add_sub_cancel_left] using congrArg (fun k : ℕ => k - s) h

/-- Inverse moments of the residual under the concrete fresh-row Gaussian law.
The remaining rows are fixed; no assertion of pivoted conditional Gaussianity
is made here. -/
theorem residual_inverse_norm_moment {s n : ℕ} (B : RectMat s n) (hB : (gram B).PosDef)
    (q : ℕ) (hdq : 2 * q < n - s) :
    Integrable (fun y : Fin n → ℝ => (‖residual B y‖ ^ (2 * q))⁻¹) (gaussianVector n) ∧
      (∫ y : Fin n → ℝ, (‖residual B y‖ ^ (2 * q))⁻¹ ∂gaussianVector n) =
        (∏ j ∈ Finset.range q, (((n - s : ℕ) : ℝ) - 2 * (j + 1)))⁻¹ := by
  have hdim := rowSpan_orthogonal_finrank B hB
  have hm : MeasurePreserving (toLp 2) (gaussianVector n) (stdGaussian (E n)) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  obtain ⟨hi, he⟩ := projected_inverse_norm_moment (rowSpan B)ᗮ q (by rwa [hdim])
  constructor
  · simpa only [Function.comp_def, residual] using hm.integrable_comp_of_integrable hi
  · rw [← hm.map_eq, integral_map hm.measurable.aemeasurable (by fun_prop)] at he
    simpa only [hdim, residual] using he

theorem gaussian_cons_measurePreserving (s n : ℕ) :
    MeasurePreserving (fun z : (Fin n → ℝ) × RectMat s n => Fin.cons z.1 z.2)
      ((gaussianVector n).prod (gaussianRect s n)) (gaussianRect (s + 1) n) := by
  have h := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (s + 1) => gaussianVector n) 0).symm
  convert h using 1
  · funext z i
    simp [MeasurableEquiv.piFinSuccAbove]
  · rfl
  · rfl

/-- First diagonal inverse-Gram moments, with integrability proved by Fubini
and fixed-subspace residual moments. -/
theorem inverse_gram_first_moment (s n q : ℕ) (hn : s + 1 + 2 * q ≤ n) :
    Integrable (fun G : RectMat (s + 1) n => ((gram G)⁻¹ 0 0) ^ q)
      (gaussianRect (s + 1) n) ∧
    (∫ G : RectMat (s + 1) n, ((gram G)⁻¹ 0 0) ^ q ∂gaussianRect (s + 1) n) =
      (∏ j ∈ Finset.range q, (((n - s : ℕ) : ℝ) - 2 * (j + 1)))⁻¹ := by
  let C := (∏ j ∈ Finset.range q, (((n - s : ℕ) : ℝ) - 2 * (j + 1)))⁻¹
  let f := fun G : RectMat (s + 1) n => ((gram G)⁻¹ 0 0) ^ q
  let c : RectMat s n × (Fin n → ℝ) → RectMat (s + 1) n := fun z => Fin.cons z.2 z.1
  have hmp : MeasurePreserving c ((gaussianRect s n).prod (gaussianVector n))
      (gaussianRect (s + 1) n) :=
    (gaussian_cons_measurePreserving s n).comp Measure.measurePreserving_swap
  have hfm : Measurable f := by
    exact (((measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp
      ((measurable_inverse (s + 1)).comp (gram_continuous (m := s + 1) (n := n)).measurable)))).pow_const q
  have hfull : ∀ᵐ z ∂(gaussianRect s n).prod (gaussianVector n), (gram (c z)).det ≠ 0 := by
    apply ae_of_ae_map (μ := (gaussianRect s n).prod (gaussianVector n))
      (p := fun G => (gram G).det ≠ 0) hmp.measurable.aemeasurable
    rw [hmp.map_eq]
    exact gram_det_ne_zero_ae (s + 1) n (by omega)
  have hcond : ∀ᵐ B ∂gaussianRect s n,
      Integrable (fun y => f (c (B, y))) (gaussianVector n) ∧
      (∫ y, f (c (B, y)) ∂gaussianVector n) = C ∧
      (∫ y, ‖f (c (B, y))‖ ∂gaussianVector n) = C := by
    filter_upwards [Measure.ae_ae_of_ae_prod hfull, gram_posDef_ae s n (by omega)] with B hdet hB
    obtain ⟨hi, he⟩ := residual_inverse_norm_moment B hB q (by omega)
    have heq : (fun y => f (c (B, y))) =ᵐ[gaussianVector n]
        (fun y => (‖residual B y‖ ^ (2 * q))⁻¹) := by
      filter_upwards [hdet] with y hy
      dsimp only [f, c] at *
      rw [inverse_gram_first_diagonal B y hy, inv_pow, ← pow_mul]
    have hnq : (fun y => ‖f (c (B, y))‖) =ᵐ[gaussianVector n]
        (fun y => (‖residual B y‖ ^ (2 * q))⁻¹) := by
      filter_upwards [heq] with y hy
      rw [hy, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact ⟨hi.congr heq.symm, (integral_congr_ae heq).trans he,
      (integral_congr_ae hnq).trans he⟩
  have hip : Integrable (f ∘ c) ((gaussianRect s n).prod (gaussianVector n)) := by
    apply (integrable_prod_iff (hfm.comp hmp.measurable).aestronglyMeasurable).mpr
    constructor
    · exact hcond.mono fun B hB => hB.1
    · apply (integrable_const C).congr
      filter_upwards [hcond] with B hB
      exact hB.2.2.symm
  refine ⟨(hmp.integrable_comp hfm.aestronglyMeasurable).mp hip, ?_⟩
  change (∫ G, f G ∂gaussianRect (s + 1) n) = C
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hfm.aestronglyMeasurable]
  change (∫ z, (f ∘ c) z ∂(gaussianRect s n).prod (gaussianVector n)) = C
  rw [integral_prod _ hip]
  calc
    _ = ∫ _B : RectMat s n, C ∂gaussianRect s n :=
      integral_congr_ae (hcond.mono fun B hB => hB.2.1)
    _ = C := by
      simp

private def isometryMatrix {d : ℕ} (f : E d ≃ₗᵢ[ℝ] E d) : Mat d :=
  (Matrix.toEuclideanLin (𝕜 := ℝ)).symm f.toLinearMap

private theorem isometryMatrix_unitary {d : ℕ} (f : E d ≃ₗᵢ[ℝ] E d) :
    isometryMatrix f ∈ Matrix.unitaryGroup (Fin d) ℝ := by
  exact f.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin d) ℝ)
    (EuclideanSpace.basisFun (Fin d) ℝ)

private theorem isometryMatrix_apply {d : ℕ} (f : E d ≃ₗᵢ[ℝ] E d) (v : E d) :
    isometryMatrix f *ᵥ ofLp v = ofLp (f v) := by
  have h : Matrix.toEuclideanLin (isometryMatrix f) = f.toLinearMap :=
    LinearEquiv.apply_symm_apply _ _
  exact congrArg ofLp (congrArg (fun T : E d →ₗ[ℝ] E d => T v) h)

private theorem rotateColumns_matrix {m n : ℕ} (f : E m ≃ₗᵢ[ℝ] E m) (G : RectMat m n) :
    Matrix.of (rotateColumns f G) = isometryMatrix f * Matrix.of G := by
  ext i j
  exact (congrFun (isometryMatrix_apply f (toLp 2 (fun k => G k j))) i).symm

private theorem gram_rotateColumns {m n : ℕ} (f : E m ≃ₗᵢ[ℝ] E m) (G : RectMat m n) :
    gram (rotateColumns f G) = isometryMatrix f * gram G * (isometryMatrix f)ᴴ := by
  simp only [gram, rotateColumns_matrix, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem inverse_gram_rotateColumns {m n : ℕ} (f : E m ≃ₗᵢ[ℝ] E m) (G : RectMat m n) :
    (gram (rotateColumns f G))⁻¹ = isometryMatrix f * (gram G)⁻¹ * (isometryMatrix f)ᴴ := by
  have hu := isometryMatrix_unitary f
  have hi : (isometryMatrix f)⁻¹ = (isometryMatrix f)ᴴ :=
    Matrix.inv_eq_right_inv (Unitary.mul_star_self_of_mem hu)
  have hhi : ((isometryMatrix f)ᴴ)⁻¹ = isometryMatrix f :=
    Matrix.inv_eq_right_inv (Unitary.star_mul_self_of_mem hu)
  rw [gram_rotateColumns, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hi, hhi, Matrix.mul_assoc]

/-- Exact simultaneous transformation of a vector and all row coordinates;
it holds even at singular matrices because the ordinary inverse is totalized. -/
theorem directionalQuadratic_rotateColumns {m n : ℕ} (f : E m ≃ₗᵢ[ℝ] E m)
    (G : RectMat m n) (v : E m) :
    directionalQuadratic (rotateColumns f G) (f v) = directionalQuadratic G v := by
  have hu := isometryMatrix_unitary f
  have hunit : (isometryMatrix f)ᴴ * isometryMatrix f = 1 :=
    Unitary.star_mul_self_of_mem hu
  have hback : (isometryMatrix f)ᴴ *ᵥ ofLp (f v) = ofLp v := by
    rw [← isometryMatrix_apply f v, Matrix.mulVec_mulVec, hunit,
      Matrix.one_mulVec]
  unfold directionalQuadratic
  rw [inverse_gram_rotateColumns, ← Matrix.mulVec_mulVec, hback, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  change ((isometryMatrix f)ᴴ *ᵥ ofLp (f v)) ⬝ᵥ ((gram G)⁻¹ *ᵥ ofLp v) = _
  rw [hback]

/-- Exact inverse Gram moment in any deterministic direction. -/
theorem directional_inverse_gram_moment_succ {s n q : ℕ}
    (hn : s + 1 + 2 * q ≤ n) (v : E (s + 1)) :
    Integrable (fun G : RectMat (s + 1) n => directionalQuadratic G v ^ q)
      (gaussianRect (s + 1) n) ∧
    (∫ G : RectMat (s + 1) n, directionalQuadratic G v ^ q
      ∂gaussianRect (s + 1) n) =
      ‖v‖ ^ (2 * q) / ∏ j ∈ Finset.range q, (((n - s : ℕ) : ℝ) - 2 * (j + 1)) := by
  let w : E (s + 1) := EuclideanSpace.single 0 ‖v‖
  have hnw : ‖v‖ = ‖w‖ := by simp [w, PiLp.norm_single]
  let f : E (s + 1) ≃ₗᵢ[ℝ] E (s + 1) := (ℝ ∙ (v - w))ᗮ.reflection
  have hfv : f v = w := Submodule.reflection_sub hnw
  have hs (G : RectMat (s + 1) n) :
      directionalQuadratic G w ^ q = ‖v‖ ^ (2 * q) * ((gram G)⁻¹ 0 0) ^ q := by
    simp only [directionalQuadratic, w, PiLp.ofLp_single, Matrix.mulVec_single,
      single_dotProduct]
    change (‖v‖ * ((gram G)⁻¹ 0 0 * ‖v‖)) ^ q = _
    rw [mul_comm ((gram G)⁻¹ 0 0)]
    rw [← mul_assoc, ← pow_two, mul_pow, ← pow_mul]
  have heq (G : RectMat (s + 1) n) :
      directionalQuadratic G v ^ q =
        ‖v‖ ^ (2 * q) * ((gram (rotateColumns f G))⁻¹ 0 0) ^ q := by
    rw [← directionalQuadratic_rotateColumns f G v, hfv, hs]
  obtain ⟨hi, he⟩ := inverse_gram_first_moment s n q hn
  let g : RectMat (s + 1) n → ℝ := fun G => ‖v‖ ^ (2 * q) * ((gram G)⁻¹ 0 0) ^ q
  have hgi : Integrable g (gaussianRect (s + 1) n) := hi.const_mul _
  have hgm : AEStronglyMeasurable g (gaussianRect (s + 1) n) := hgi.aestronglyMeasurable
  have hmp := rotateColumns_measurePreserving (n := n) f
  have hfun : (fun G : RectMat (s + 1) n => directionalQuadratic G v ^ q) =
      g ∘ rotateColumns f := funext heq
  rw [hfun]
  refine ⟨hmp.integrable_comp_of_integrable hgi, ?_⟩
  have hmap : (∫ G, (g ∘ rotateColumns f) G ∂gaussianRect (s + 1) n) =
      ∫ G, g G ∂gaussianRect (s + 1) n := by
    have hgm' : AEStronglyMeasurable g ((gaussianRect (s + 1) n).map (rotateColumns f)) := by
      simpa only [hmp.map_eq] using hgm
    simpa only [Function.comp_def, hmp.map_eq] using
      (integral_map hmp.measurable.aemeasurable hgm').symm
  rw [hmap]
  change (∫ G, ‖v‖ ^ (2 * q) * ((gram G)⁻¹ 0 0) ^ q ∂gaussianRect (s + 1) n) = _
  rw [integral_const_mul, he]
  exact (div_eq_mul_inv _ _).symm

/-- The dimension is cast after natural subtraction, exactly as in the
regression specification; all denominator factors are positive under `hn`. -/
theorem directional_inverse_gram_moment {m n q : ℕ} (hm : 0 < m)
    (hn : m + 2 * q ≤ n) (v : E m) :
    Integrable (fun G : RectMat m n => directionalQuadratic G v ^ q) (gaussianRect m n) ∧
    (∫ G : RectMat m n, directionalQuadratic G v ^ q ∂gaussianRect m n) =
      ‖v‖ ^ (2 * q) / ∏ j ∈ Finset.range q, (((n - m + 1 : ℕ) : ℝ) - 2 * (j + 1)) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hd : n - s = n - (s + 1) + 1 := by omega
  simpa only [Nat.succ_eq_add_one, hd] using directional_inverse_gram_moment_succ hn v

#assert_trust kernel measurable_inverse
#assert_trust kernel directionalQuadratic_measurable
#assert_trust kernel gaussian_uncurry
#assert_trust kernel gaussian_transpose
#assert_trust kernel gaussian_coordinateIsometry
#assert_trust kernel gram_posDef_ae
#assert_trust kernel gram_det_ne_zero_ae
#assert_trust kernel rotateRows_measurePreserving
#assert_trust kernel rotateColumns_measurePreserving
#assert_trust kernel inverse_gram_first_diagonal
#assert_trust kernel stdGaussian_projection
#assert_trust kernel projected_inverse_norm_moment
#assert_trust kernel rowSpan_orthogonal_finrank
#assert_trust kernel residual_inverse_norm_moment
#assert_trust kernel gaussian_cons_measurePreserving
#assert_trust kernel inverse_gram_first_moment
#assert_trust kernel directionalQuadratic_rotateColumns
#assert_trust kernel directional_inverse_gram_moment_succ
#assert_trust kernel directional_inverse_gram_moment
#print axioms gram_posDef_ae
#print axioms rotateColumns_measurePreserving
#print axioms inverse_gram_first_diagonal
#print axioms projected_inverse_norm_moment
#print axioms residual_inverse_norm_moment
#print axioms inverse_gram_first_moment
#print axioms directionalQuadratic_rotateColumns
#print axioms directional_inverse_gram_moment
end NLA.IE06.GaussianRegression
