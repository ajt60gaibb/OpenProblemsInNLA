import NLA.IE22.VarianceTensorization
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Var[f; μ.prod ν] = (∫ x, Var[fun y => f (x,y); ν] ∂μ) +
      Var[fun x => ∫ y, f (x,y) ∂ν; μ] :=
  NLA.IE22.bounded_variance_prod_decomposition μ ν f hf C hb

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Var[fun x => ∫ y, f (x,y) ∂ν; μ] ≤ ∫ y, Var[fun x => f (x,y); μ] ∂ν :=
  NLA.IE22.bounded_variance_integral_le μ ν f hf C hb

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Var[f; μ.prod ν] ≤ (∫ x, Var[fun y => f (x,y); ν] ∂μ) +
      ∫ y, Var[fun x => f (x,y); μ] ∂ν :=
  NLA.IE22.bounded_variance_prod_le μ ν f hf C hb

example (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d : ℕ) (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Var[f; Measure.pi (fun _ : Fin d => μ)] ≤
      ∑ i : Fin d, ∫ x, Var[fun t => f (Function.update x i t); μ]
        ∂Measure.pi (fun _ : Fin d => μ) :=
  NLA.IE22.bounded_variance_pi μ d f hf C hb

example (d : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hf : Measurable f) (hbounded : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    Var[f; Measure.pi (fun _ : Fin d => gaussianReal 0 1)] ≤
      ∑ i : Fin d, ∫ x, Var[fun t => f (Function.update x i t); gaussianReal 0 1]
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) :=
  NLA.IE22.gaussian_variance_tensorization d f hf hbounded

example (d : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hf : Measurable f) (hbounded : ∃ C : ℝ, ∀ x, |f x| ≤ C) (i : Fin d) :
    Integrable (fun x => Var[fun t => f (Function.update x i t); gaussianReal 0 1])
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) :=
  NLA.IE22.gaussian_coordinate_variance_integrable d f hf hbounded i

example (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d : ℕ) (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (i : Fin d) :
    (∫ x, ∫ t, f (Function.update x i t) ∂μ
      ∂Measure.pi (fun _ : Fin d => μ)) =
        ∫ x, f x ∂Measure.pi (fun _ : Fin d => μ) :=
  NLA.IE22.bounded_integral_coordinate_resampling μ d f hf C hb i

example (d : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hf : Measurable f) (hbounded : ∃ C : ℝ, ∀ x, |f x| ≤ C) (i : Fin d) :
    (∫ x, ∫ t, f (Function.update x i t) ∂gaussianReal 0 1
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) =
        ∫ x, f x ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) :=
  NLA.IE22.gaussian_integral_coordinate_resampling d f hf hbounded i

#print axioms NLA.IE22.bounded_variance_prod_decomposition
#print axioms NLA.IE22.bounded_variance_integral_le
#print axioms NLA.IE22.bounded_variance_prod_le
#print axioms NLA.IE22.bounded_variance_pi
#print axioms NLA.IE22.gaussian_variance_tensorization
#print axioms NLA.IE22.gaussian_coordinate_variance_integrable

#print axioms NLA.IE22.bounded_integral_coordinate_resampling
#print axioms NLA.IE22.gaussian_integral_coordinate_resampling
