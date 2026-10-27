import NLA.Proofs.RE06.GaussianProductMoment

/-! Transport of the exact Gaussian product moment, including coefficients
which depend measurably on an independent parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem hasLaw_gaussian_product_square_integrable {a b c d : ℕ}
    (U : Matrix (Fin a) (Fin b) ℝ) (V : Matrix (Fin c) (Fin d) ℝ)
    (X : Ω → Fin b × Fin c → ℝ)
    (hX : HasLaw X (Measure.pi (fun _ : Fin b × Fin c => gaussianReal 0 1)) μ) :
    Integrable (fun ω => squaredFrobenius
      (U * Matrix.of (fun l k => X ω (l, k)) * V) 0) μ := by
  have hi := gaussian_product_square_integrable U V
  rw [← hX.map_eq] at hi
  exact hi.comp_aemeasurable hX.aemeasurable

theorem hasLaw_gaussian_product_square_integral {a b c d : ℕ}
    (U : Matrix (Fin a) (Fin b) ℝ) (V : Matrix (Fin c) (Fin d) ℝ)
    (X : Ω → Fin b × Fin c → ℝ)
    (hX : HasLaw X (Measure.pi (fun _ : Fin b × Fin c => gaussianReal 0 1)) μ) :
    ∫ ω, squaredFrobenius (U * Matrix.of (fun l k => X ω (l, k)) * V) 0 ∂μ =
      squaredFrobenius U 0 * squaredFrobenius V 0 := by
  exact (hX.integral_comp (gaussian_product_square_integrable U V).aestronglyMeasurable).trans
    (gaussian_product_square_integral U V)

theorem stream_gaussian_product_square_integrable {a b c d : ℕ}
    (U : Matrix (Fin a) (Fin b) ℝ) (V : Matrix (Fin c) (Fin d) ℝ) (offset : ℕ) :
    Integrable (fun ω => squaredFrobenius (U * gaussianBlock b c offset ω * V) 0)
      GaussianLaw := by
  have h := hasLaw_gaussian_product_square_integrable
    (Ω := ℕ → ℝ) (μ := GaussianLaw) (a := a) (b := b) (c := c) (d := d)
    U V (fun ω p => gaussianBlock b c offset ω p.1 p.2)
    (gaussianBlock_entries_hasLaw b c offset)
  exact h

theorem stream_gaussian_product_square_integral {a b c d : ℕ}
    (U : Matrix (Fin a) (Fin b) ℝ) (V : Matrix (Fin c) (Fin d) ℝ) (offset : ℕ) :
    ∫ ω, squaredFrobenius (U * gaussianBlock b c offset ω * V) 0 ∂GaussianLaw =
      squaredFrobenius U 0 * squaredFrobenius V 0 := by
  have h := hasLaw_gaussian_product_square_integral
    (Ω := ℕ → ℝ) (μ := GaussianLaw) (a := a) (b := b) (c := c) (d := d)
    U V (fun ω p => gaussianBlock b c offset ω p.1 p.2)
    (gaussianBlock_entries_hasLaw b c offset)
  exact h

section Fubini
variable {α : Type*} [MeasurableSpace α] (ν : Measure α)

/-- Entrywise measurability suffices; no matrix measurable-space instance is
introduced. Both fixed factors may depend on the same independent parameter. -/
theorem measurable_gaussian_product_energy {a b c d : ℕ}
    (U : α → Matrix (Fin a) (Fin b) ℝ) (V : α → Matrix (Fin c) (Fin d) ℝ)
    (hU : ∀ i l, Measurable (fun y => U y i l))
    (hV : ∀ k j, Measurable (fun y => V y k j)) :
    Measurable (fun p : α × (Fin b × Fin c → ℝ) => squaredFrobenius
      (U p.1 * Matrix.of (fun l k => p.2 (l, k)) * V p.1) 0) := by
  have hu (i : Fin a) (l : Fin b) :
      Measurable (fun p : α × (Fin b × Fin c → ℝ) => U p.1 i l) :=
    (hU i l).comp measurable_fst
  have hv (k : Fin c) (j : Fin d) :
      Measurable (fun p : α × (Fin b × Fin c → ℝ) => V p.1 k j) :=
    (hV k j).comp measurable_fst
  simp only [squaredFrobenius, Matrix.zero_apply, sub_zero, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

/-- Fubini's integrability criterion is discharged by the exact inner moment.
The premise is integrability of the resulting coefficient energy product. -/
theorem gaussian_product_fubini_integrable {a b c d : ℕ}
    (U : α → Matrix (Fin a) (Fin b) ℝ) (V : α → Matrix (Fin c) (Fin d) ℝ)
    (hU : ∀ i l, Measurable (fun y => U y i l))
    (hV : ∀ k j, Measurable (fun y => V y k j))
    (henergy : Integrable (fun y => squaredFrobenius (U y) 0 * squaredFrobenius (V y) 0) ν) :
    Integrable (fun p : α × (Fin b × Fin c → ℝ) => squaredFrobenius
      (U p.1 * Matrix.of (fun l k => p.2 (l, k)) * V p.1) 0)
      (ν.prod (Measure.pi (fun _ : Fin b × Fin c => gaussianReal 0 1))) := by
  apply (integrable_prod_iff (measurable_gaussian_product_energy U V hU hV).aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ (fun y => gaussian_product_square_integrable (U y) (V y))
  · have he (y : α) :
        (∫ x : Fin b × Fin c → ℝ,
          ‖squaredFrobenius (U y * Matrix.of (fun l k => x (l, k)) * V y) 0‖
          ∂Measure.pi (fun _ : Fin b × Fin c => gaussianReal 0 1)) =
          squaredFrobenius (U y) 0 * squaredFrobenius (V y) 0 := by
      calc
        _ = ∫ x : Fin b × Fin c → ℝ,
            squaredFrobenius (U y * Matrix.of (fun l k => x (l, k)) * V y) 0
            ∂Measure.pi (fun _ : Fin b × Fin c => gaussianReal 0 1) := by
          apply integral_congr_ae
          filter_upwards [] with x
          apply Real.norm_of_nonneg
          exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        _ = _ := gaussian_product_square_integral (U y) (V y)
    simpa only [he] using henergy

theorem gaussian_product_fubini_integral {a b c d : ℕ}
    (U : α → Matrix (Fin a) (Fin b) ℝ) (V : α → Matrix (Fin c) (Fin d) ℝ)
    (hU : ∀ i l, Measurable (fun y => U y i l))
    (hV : ∀ k j, Measurable (fun y => V y k j))
    (henergy : Integrable (fun y => squaredFrobenius (U y) 0 * squaredFrobenius (V y) 0) ν) :
    ∫ p : α × (Fin b × Fin c → ℝ), squaredFrobenius
      (U p.1 * Matrix.of (fun l k => p.2 (l, k)) * V p.1) 0
      ∂ν.prod (Measure.pi (fun _ : Fin b × Fin c => gaussianReal 0 1)) =
      ∫ y, squaredFrobenius (U y) 0 * squaredFrobenius (V y) 0 ∂ν := by
  rw [integral_prod _ (gaussian_product_fubini_integrable ν U V hU hV henergy)]
  exact integral_congr_ae (ae_of_all _ (fun y => gaussian_product_square_integral (U y) (V y)))

end Fubini

#assert_trust kernel hasLaw_gaussian_product_square_integrable
#assert_trust kernel hasLaw_gaussian_product_square_integral
#assert_trust kernel stream_gaussian_product_square_integrable
#assert_trust kernel stream_gaussian_product_square_integral
#assert_trust kernel measurable_gaussian_product_energy
#assert_trust kernel gaussian_product_fubini_integrable
#assert_trust kernel gaussian_product_fubini_integral
#print axioms hasLaw_gaussian_product_square_integrable
#print axioms hasLaw_gaussian_product_square_integral
#print axioms stream_gaussian_product_square_integrable
#print axioms stream_gaussian_product_square_integral
#print axioms measurable_gaussian_product_energy
#print axioms gaussian_product_fubini_integrable
#print axioms gaussian_product_fubini_integral
end NLA.Proofs.RE06
