import NLA.TR06.LinearNorm
noncomputable section
open scoped ENNReal
open NLA.TR06
example {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}
    (dφ : EuclideanSpace ℝ (Fin k) →L[ℝ] Tensor ℝ d n)
    (dg : EuclideanSpace ℝ (Fin k) →L[ℝ] AngularOutput d n r)
    (hinj : Function.Injective dφ) :
    derivativeRatio dφ dg = ENNReal.ofReal ‖inducedDerivative dφ dg hinj‖ := NLA.TR06.derivativeRatio_eq_operatorNorm
