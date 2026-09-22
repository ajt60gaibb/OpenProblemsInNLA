import NLA.IE21.UniformTrimming
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NLA.IE21
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1) :
    (matrixLaw m n).real (GoodEvent θ m n t ε δ)ᶜ ≤ finiteFailure m n t ε δ := by
  exact uniform_trim_concentration θ hθ m n hm hn t ε δ ht hε hδ
end NLA.IE21
