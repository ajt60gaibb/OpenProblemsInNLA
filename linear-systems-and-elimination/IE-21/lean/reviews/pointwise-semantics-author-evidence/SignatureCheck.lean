import NLA.IE21.PointwiseTrimmingSemantics
set_option autoImplicit false
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace NLA.IE21
example {m : ℕ} (k : ℕ) (hk : k ≤ m)
    (c : ℝ) (hc : 0 ≤ c) (y : Fin m → ℝ) :
    finiteTrim k (fun i => c * y i) = c * finiteTrim k y := by
  exact finiteTrim_smul_nonneg k hk c hc y

example {m n : ℕ} (θ : ℝ)
    (hθ : 0 < θ ∧ θ < 1) (A : Mat m n) (x : Space n) :
    directionalTrim θ A x =
      finiteTrim (retainedRows θ m) (fun i => directionalEnergy x (matrixRow A i)) / m := by
  exact directionalTrim_eq_energy_trim θ hθ A x

end NLA.IE21
