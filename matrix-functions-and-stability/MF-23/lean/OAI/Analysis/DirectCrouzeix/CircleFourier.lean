import OAI.Analysis.DirectCrouzeix.Sharpness

namespace OAI

universe u_47 u_48 u_49 u_50 u_51 u_52 u_53 u_54 u_55 u_56 u_57 u_58 u_59 u_60 u_61 u_62 u_63 u_64
  u_65 u_66 u_67 u_68 u_69 u_70 u_71 u_72

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem continuous_integrable_compact {α : Type u_47} {E : Type u_48} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem continuous_integral_compact {α : Type u_49} {β : Type u_50} {E : Type u_51}
    [TopologicalSpace α] [FirstCountableTopology α] [LocallyCompactSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    [CompactSpace β] [SecondCountableTopology β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure β) [IsFiniteMeasure μ] {f : α → β → E}
    (hf : Continuous f.uncurry) : Continuous (fun x => ∫ y, f x y ∂μ) := by
  simpa using continuous_parametric_integral_of_continuous (μ := μ) hf isCompact_univ

theorem markov_kernel_contraction {α : Type u_52} {β : Type u_53} {E : Type u_54}
    [MetricSpace α] [MeasurableSpace α] [BorelSpace α] [CompactSpace α]
    [SecondCountableTopology α]
    [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [CompactSpace β]
    [SecondCountableTopology β]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (K : α → β → ℝ) (u : α → E)
    (hK : Continuous K.uncurry) (hu : Continuous u)
    (hpos : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∫ x, K x y ∂μ = 1)
    (hrow : ∀ x, ∫ y, K x y ∂ν = 1) :
    (∫ y, ‖∫ x, K x y • u x ∂μ‖ ^ 2 ∂ν) ≤ ∫ x, ‖u x‖ ^ 2 ∂μ := by
  have hKcol (y : β) : Continuous (fun x => K x y) :=
    hK.comp (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun y => ∫ x, K x y • u x ∂μ) := by
    apply continuous_integral_compact
    exact (hK.comp continuous_swap).smul (hu.comp continuous_snd)
  have hs : Integrable (fun p : α × β => K p.1 p.2 * ‖u p.1‖ ^ 2) (μ.prod ν) :=
    continuous_integrable_compact _ (hK.mul ((hu.comp continuous_fst).norm.pow 2))
  calc
    _ ≤ ∫ y, ∫ x, K x y * ‖u x‖ ^ 2 ∂μ ∂ν := by
      apply integral_mono (continuous_integrable_compact _ (hT.norm.pow 2))
        hs.integral_prod_right
      intro y
      exact weighted_integral_norm_sq_le μ (fun x => K x y) u (fun x => hpos x y)
        (continuous_integrable_compact _ (hKcol y))
        (continuous_integrable_compact _ ((hKcol y).smul hu))
        (continuous_integrable_compact _ ((hKcol y).mul (hu.norm.pow 2))) (hcol y)
    _ = ∫ x, ∫ y, K x y * ‖u x‖ ^ 2 ∂ν ∂μ := (integral_integral_swap hs).symm
    _ = _ := by simp_rw [integral_mul_const, hrow, one_mul]

abbrev BoundaryCircle := AddCircle (1 : ℝ)

abbrev circleMeasure : Measure BoundaryCircle := AddCircle.haarAddCircle

theorem scalar_circle_parseval (f : BoundaryCircle → ℂ) (hf : Continuous f) :
    HasSum (fun k : ℤ => ‖fourierCoeff f k‖ ^ 2)
      (∫ t, ‖f t‖ ^ 2 ∂circleMeasure) := by
  let F : C(BoundaryCircle, ℂ) := ⟨f, hf⟩
  have h := hasSum_sq_fourierCoeff (ContinuousMap.toLp 2 circleMeasure ℂ F)
  simp_rw [fourierCoeff_toLp] at h
  have hi : (∫ t, ‖(ContinuousMap.toLp 2 circleMeasure ℂ F) t‖ ^ 2 ∂circleMeasure) =
      ∫ t, ‖f t‖ ^ 2 ∂circleMeasure := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (𝕜 := ℂ) circleMeasure F]
      with t ht
    rw [ht]
    rfl
  rwa [hi] at h

theorem fourierCoeff_euclidean_apply {ι : Type u_55} [Fintype ι]
    (f : BoundaryCircle → EuclideanSpace ℂ ι) (hf : Continuous f)
    (k : ℤ) (i : ι) : (fourierCoeff f k) i = fourierCoeff (fun t => f t i) k := by
  have hi : Integrable (fun t => fourier (-k) t • f t) circleMeasure :=
    (continuous_integrable_compact _ hf).fourier_smul _
  exact ((EuclideanSpace.proj i).integral_comp_comm hi).symm

theorem euclidean_circle_parseval {ι : Type u_56} [Fintype ι]
    (f : BoundaryCircle → EuclideanSpace ℂ ι) (hf : Continuous f) :
    HasSum (fun k : ℤ => ‖fourierCoeff f k‖ ^ 2)
      (∫ t, ‖f t‖ ^ 2 ∂circleMeasure) := by
  have h (i : ι) := scalar_circle_parseval (fun t => f t i)
    ((PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).comp hf)
  have hs := hasSum_sum (s := Finset.univ) (fun i _ => h i)
  simp_rw [← fourierCoeff_euclidean_apply f hf] at hs
  simp_rw [EuclideanSpace.norm_sq_eq]
  have hi (i : ι) : Integrable (fun t => ‖f t i‖ ^ 2) circleMeasure :=
    continuous_integrable_compact _
      (((PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).comp hf).norm.pow 2)
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  exact hs

def hsCLM {ι : Type u_57} {κ : Type u_58} [Fintype ι] [Fintype κ] :
    Matrix ι κ ℂ →L[ℂ] EuclideanSpace ℂ (ι × κ) :=
  LinearMap.toContinuousLinearMap
    { toFun := hsVector
      map_add' := by intros; ext i; rfl
      map_smul' := by intros; ext i; rfl }

@[simp] theorem hsCLM_apply {ι : Type u_59} {κ : Type u_60} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : hsCLM A = hsVector A := rfl

theorem continuous_hsSq {ι : Type u_61} {κ : Type u_62} [Fintype ι] [Fintype κ] :
    Continuous (hsSq : Matrix ι κ ℂ → ℝ) := by
  change Continuous (fun M : Matrix ι κ ℂ => hsSq M)
  simp_rw [hsSq_eq_norm_hsVector_sq]
  exact hsCLM.continuous.norm.pow 2

theorem fourierCoeff_clm {E : Type u_63} {F : Type u_64} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (f : BoundaryCircle → E) (hf : Continuous f) (k : ℤ) :
    fourierCoeff (fun t => L (f t)) k = L (fourierCoeff f k) := by
  unfold fourierCoeff
  simp_rw [← map_smul]
  exact L.integral_comp_comm ((continuous_integrable_compact _ hf).fourier_smul _)

theorem matrix_circle_parseval {ι : Type u_65} {κ : Type u_66} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (f : BoundaryCircle → Matrix ι κ ℂ) (hf : Continuous f) :
    HasSum (fun k : ℤ => hsSq (fourierCoeff f k))
      (∫ t, hsSq (f t) ∂circleMeasure) := by
  have hp := euclidean_circle_parseval (fun t => hsCLM (f t)) (hsCLM.continuous.comp hf)
  simp_rw [fourierCoeff_clm hsCLM f hf, hsCLM_apply, ← hsSq_eq_norm_hsVector_sq] at hp
  exact hp

def compressionCLM {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin m) (Fin m) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun R => Yᴴ * R * X
      map_add' := by intros; simp [Matrix.mul_add,Matrix.add_mul]
      map_smul' := by intros; simp [Matrix.mul_smul,Matrix.smul_mul] }

@[simp] theorem compressionCLM_apply {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℂ)
    (R : Matrix (Fin n) (Fin n) ℂ) : compressionCLM X Y R = Yᴴ * R * X := rfl

theorem fourierCoeff_compression {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℂ)
    (R : BoundaryCircle → Matrix (Fin n) (Fin n) ℂ) (hR : Continuous R) (k : ℤ) :
    fourierCoeff (fun t => Yᴴ * R t * X) k = Yᴴ * fourierCoeff R k * X :=
  fourierCoeff_clm (compressionCLM X Y) R hR k

def conjugateTransposeCLM {ι : Type u_67} {κ : Type u_68} [Fintype ι] [Fintype κ] :
    Matrix ι κ ℂ →L[ℝ] Matrix κ ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.conjTranspose
      map_add' := by intros; simp
      map_smul' := by intros; simp }

@[simp] theorem conjugateTransposeCLM_apply {ι : Type u_69} {κ : Type u_70} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : conjugateTransposeCLM A = Aᴴ := rfl

theorem fourierCoeff_star_matrix {ι : Type u_71} {κ : Type u_72} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (f : BoundaryCircle → Matrix ι κ ℂ) (hf : Continuous f) (k : ℤ) :
    fourierCoeff (fun t => (f t)ᴴ) k = (fourierCoeff f (-k))ᴴ := by
  unfold fourierCoeff
  have hh := conjugateTransposeCLM.integral_comp_comm
    ((continuous_integrable_compact _ hf).fourier_smul (-(-k)))
  simp only [conjugateTransposeCLM_apply] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards with t
  simp only [neg_neg,Matrix.conjTranspose_smul,starRingEnd_apply,fourier_neg]

end DirectCrouzeix

end

end OAI
