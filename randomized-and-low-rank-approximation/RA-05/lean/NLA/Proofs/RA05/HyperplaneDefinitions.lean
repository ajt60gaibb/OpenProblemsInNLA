import NLA.Statements.RA05
import NLA.Statements.RA06
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact complementary rank-one projector used to transfer the actual RA05
strong-coreset guarantee to the actual RA06 all-vector energy. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
namespace NLA.Proofs.RA05

/-- Orthogonal projection onto the hyperplane normal to a unit vector. -/
noncomputable def UnitHyperplane {d : ℕ} (x : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  1 - Matrix.vecMulVec x x

/-- The arbitrary nonnegative original-row weighted energy. This is not
restricted to a Bernoulli sampler or inverse-probability weights. -/
noncomputable def WeightedInputEnergy {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p : ℝ) (w : Fin n → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∑ i, w i * Real.rpow |NLA.Statements.RA06.RowValue A i x| p

end NLA.Proofs.RA05
