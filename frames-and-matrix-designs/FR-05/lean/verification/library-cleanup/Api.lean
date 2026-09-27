import NLA.FR05.Geometry.Obstruction
import NLA.FR05.Measure.Comparison
import NLA.FR05.Gaussian.GaussianGram
import NLA.FR05.SmallBall.GaussianSmallBall
import NLA.FR05.Overlap.HaarCorner
import NLA.FR05.Overlap.Spectrum
import NLA.FR05.SmallBall.PhaseAbsolute
import NLA.FR05.Likelihood.ScalarTaylor
import NLA.FR05.Planted.SourceLocalControl

/-!
# Regression tests for the reusable APIs

The examples exercise the reusable results independently of the final assembly,
including rectangular maps, singular Gram matrices, empty Gaussian blocks, and
zero variance. Declaration linters are limited to the curated source modules.
-/

open MeasureTheory NLA.FR05
open scoped ENNReal Matrix

-- The Gaussian tail is a probability law, including zero-dimensional tails,
-- without installing a local instance in every proof.
example (n : ℕ) : IsProbabilityMeasure (standardComplexGaussianTail n) := inferInstance

-- Canonical coordinate and seed equations are available to simp.
example {n : ℕ} (u v : ℂ) (w : Signal n) :
    joinTwo u v w ⟨0, by lia⟩ = u := by simp

example {n : ℕ} (u v : ℂ) (w : Signal n) : joinTwo u v w 1 = v := by simp

example {n : ℕ} (r : PlantedRow n) : plantedEquation r 0 0 0 0 = r.imbalance := by simp

-- Continuity of the projection is registered with fun_prop.
example {n : ℕ} {ι : Type*} (B : Matrix (Fin n) ι ℂ) :
    Continuous (gaussianMatrixProjection B) := by fun_prop

-- Integrability supplies a.e. measurability and finite density mass; no separate
-- measurability, finite-density, nonempty-index, or probability assumptions.
example {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (f : X → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f μ) :
    Measure.pi (fun _ : ι ↦ μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) =
      (Measure.pi (fun _ : ι ↦ μ)).withDensity
        (fun a ↦ ENNReal.ofReal (∏ i, f (a i))) :=
  Measure.pi_withDensity_ofReal μ f hf0 hfi

-- A lower singular-value bound needs no decidable equality on the index type.
example {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (s : ℝ) :
    HasEuclideanLowerBound A s ↔
      ∀ x : EuclideanSpace ℝ ι, s * ‖x‖ ≤ ‖euclideanMap A x‖ := Iff.rfl

-- Rectangular matrix products do not require invertibility or dimension inequalities.
example {m d e : ℕ} (A : Frame m d) (B : Matrix (Fin d) (Fin e) ℂ)
    (x y : Signal e) :
    SameMeasurements (A * B) x y ↔ SameMeasurements A (B *ᵥ x) (B *ᵥ y) :=
  sameMeasurements_mul A B x y

-- The simp API transports global phase through any complex-linear equivalence.
example {d e : ℕ} (f : Signal d ≃ₗ[ℂ] Signal e) (x y : Signal d) :
    GloballyPhased (f x) (f y) ↔ GloballyPhased x y := by
  simp

-- The scaling need not be unitary; no positive-dimension assumption is needed.
example {m d : ℕ} (A : Frame m d) :
    PhaseRetrievalInjective (A * Matrix.diagonal (fun _ : Fin d ↦ (2 : ℂ))) ↔
      PhaseRetrievalInjective A :=
  phaseRetrievalInjective_mul_diagonal A _ (by intro j; norm_num)

-- The ambient measure need not be finite: only its restriction to the event is finite.
example {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : Set X)
    [IsFiniteMeasure (μ.restrict s)] {f : X → ℝ} (hf : MemLp f 2 (μ.restrict s)) :
    |∫ x in s, f x ∂μ| ≤ Real.sqrt ((∫ x in s, f x ^ 2 ∂μ) * μ.real s) :=
  abs_setIntegral_le_sqrt_setIntegral_sq s hf

-- Three arbitrary spaces; no group, probability, or integrability assumption.
example {G X Y : Type*} [MeasurableSpace G] [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure G) (μ : Measure X) (ν : Measure Y) [SFinite ρ] [SFinite μ] [SFinite ν]
    (T : G → Y → X) (hT : Measurable (Function.uncurry T))
    (d : G → X → ℝ≥0∞) (hd : Measurable (Function.uncurry d))
    (hmap : ∀ g, ν.map (T g) = μ.withDensity (d g)) :
    (ρ.prod ν).map (Function.uncurry T) = μ.withDensity (fun x ↦ ∫⁻ g, d g x ∂ρ) :=
  Measure.map_prod_eq_withDensity ρ μ ν T hT d hd hmap

-- Keep the existing application-facing helper names available as well.
example {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : MemLp f 2 μ) (s : Set X) :
    |∫ x in s, f x ∂μ| ≤ Real.sqrt ((∫ x, f x ^ 2 ∂μ) * μ.real s) :=
  NLA.FR05.abs_setIntegral_le_sqrt_second_moment hf s

-- Splitting off an empty block needs no positive-dimension assumption.
example (n : ℕ) :
    (standardComplexGaussianTail n).map (splitGaussianSum n 0) =
      (standardComplexGaussianTail n).prod (standardComplexGaussianTail 0) := by
  simpa using standardComplexGaussianTail_map_splitSum n 0

-- Defining the coordinate projection and proving continuity do not need finite output indices.
example {n : ℕ} {ι : Type*} (B : Matrix (Fin n) ι ℂ) :
    Continuous (gaussianMatrixProjection B) := continuous_gaussianMatrixProjection B

-- Equal Gram matrices suffice; neither matrix needs full rank or the same row count.
example {n m : ℕ} {ι : Type*} [Finite ι]
    (B : Matrix (Fin n) ι ℂ) (C : Matrix (Fin m) ι ℂ) (h : Bᴴ * B = Cᴴ * C) :
    (standardComplexGaussianTail n).map (gaussianMatrixProjection B) =
      (standardComplexGaussianTail m).map (gaussianMatrixProjection C) :=
  gaussianMatrixProjection_law_eq_of_gram B C h

-- The projection identity packages both measurability and equality of laws.
example {n : ℕ} (z : Signal n) :
    MeasurePreserving (fun w : Signal n ↦ (star w ⬝ᵥ z).re)
      (standardComplexGaussianTail n)
      (ProbabilityTheory.gaussianReal 0 (signalEnergy z / 2).toNNReal) :=
  measurePreserving_real_star_dotProduct z

-- The variance-uniform estimate includes the Dirac (zero-variance) case.
example (m u t : ℝ) (ht : 0 < t) (hm : t ≤ |m|) (hu : 2 * u ≤ t) :
    ProbabilityTheory.gaussianReal 0 0 {x : ℝ | |m + x| ≤ u} ≤
      ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) :=
  gaussianReal_abs_add_smallBall_uniform m u t ht hm hu

-- The shared spectral identity is not tied to Fin n, positivity, or a fixed scalar.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (q : ℝ) :
    Matrix.det (1 + (q : ℂ) • A) =
      ((∏ i, (1 + q * hA.eigenvalues i) : ℝ) : ℂ) :=
  hA.det_one_add_smul_eq_prod q

-- The Haar-corner identification also includes the smallest allowed dimension.
example : sourceOverlapLaw 2 (by lia) =
    (sourceUnitaryLaw 2).map (sourceHaarCorner (by lia)) :=
  sourceOverlapLaw_eq_haarCorner (by lia)

-- The shared phase identity applies to arbitrary measurable events, not just cosine bands.
example (s : Set (AddCircle (2 * Real.pi))) (hs : MeasurableSet s) :
    sourceUniformInterval 0 (2 * Real.pi)
      (Set.Icc 0 (2 * Real.pi) ∩ (fun x : ℝ ↦ (x : AddCircle (2 * Real.pi))) ⁻¹' s) =
      phaseCircleMeasure s :=
  sourceUniformInterval_phase_preimage s hs

-- With no odd term, the factorised bound reduces to the quadratic exponential remainder.
example (A : ℝ) :
    |kernelEvenExp A 0 - (1 - A)| ≤ A ^ 2 * Real.exp |A| := by
  simpa using kernelEvenExp_factor_bound A 0

-- The inverse-cosine estimate also covers band endpoints outside [-1, 1].
example : Real.arccos (-2) - Real.arccos 2 ≤ Real.pi * Real.sqrt 2 :=
  arccos_gap_le_pi_sqrt 2 (-2) 2 (by norm_num) (by norm_num) (by norm_num)

-- A zero-width band retains its zero-measure bound, even outside the cosine range.
example : sourceUniformInterval 0 (2 * Real.pi) (cosineBandPhaseSublevel 3 0) = 0 := by
  apply le_antisymm _ bot_le
  simpa using sourceUniformInterval_cosineBandPhaseSublevel_le_sqrt 3 0 (by norm_num)

-- The addition-formula reduction includes a constant polynomial (zero amplitude).
example (a φ : ℝ) : affineTrig a 0 0 φ =
    a + affineTrigAmplitude 0 0 * Real.cos (affineTrigPhase 0 0 + φ) :=
  affineTrig_cosine_normalForm a 0 0 φ

-- The norm comparison does not assume a nonempty coordinate type.
example (v : Fin 0 → ℝ) : ‖WithLp.toLp 2 v‖ ≤ Real.sqrt 0 * 0 := by
  simpa using euclideanNorm_le_sqrt_card_mul_of_abs_le v (C := 0)
    (by norm_num) (fun i ↦ Fin.elim0 i)

-- Record the improved scalar constant without changing the later paper-facing constants.
example {ρ T A B : ℝ} (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 128) (hT : 0 ≤ T)
    (hA : |A| ≤ 4 * ρ ^ 2 * T) (hB : |B| ≤ 4 * ρ * T) :
    |kernelEvenExp A B - (1 - A + B ^ 2 / 2)| ≤
      304 * ρ ^ 4 * (1 + T) ^ 4 * Real.exp (T / 8) :=
  kernel_even_exp_remainder hρ hρsmall hT hA hB

-- The midpoint estimate works on the closed ball, including radius zero.
example {M m : ℕ} (hM : 2 ≤ M)
    (e : SourceJacobianCoordinate (sourceTailDimension M) ≃ Fin m)
    (sample : Fin m → SourcePlantedCoordinates (sourceTailDimension M))
    (hgood : SourceCoordinateSampleGood M sample)
    (x y : EuclideanSpace ℝ (SourceJacobianCoordinate (sourceTailDimension M)))
    {R : ℝ} (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖sourceEquationEuclidean e sample x - sourceEquationEuclidean e sample y -
      sourceEpsilonJacobianEuclideanApply e sample (x - y)‖ ≤
      1024 * (M : ℝ) ^ 6 * R * ‖x - y‖ :=
  sourceEquation_nonlinear_difference_le hM e sample hgood x y hR hx hy

-- "in" filters by source module, including the MeasureTheory namespace additions.
#lint docBlameThm in NLA.FR05.Definitions
#lint docBlameThm in NLA.FR05.Geometry.Obstruction
#lint docBlameThm in NLA.FR05.Measure.Comparison
#lint docBlameThm in NLA.FR05.Gaussian.GaussianFrameRows
#lint docBlameThm in NLA.FR05.Gaussian.GaussianGram
#lint docBlameThm in NLA.FR05.SmallBall.GaussianSmallBall
#lint docBlameThm in NLA.FR05.Overlap.HaarCorner
#lint docBlameThm in NLA.FR05.Overlap.Spectrum
