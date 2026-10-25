import NLA.Proofs.TR04.SVDResidual
import NLA.Proofs.TR04.SVDFrameProjection
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace TR04FrameResidualAuthor
open NLA.Proofs.TR04.SVD NLA.Computation.SVDMachine
 theorem literal_frame {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
 {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
 {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V) (r : ℕ) :
 let Q := U.submatrix id (Fin.castLE
 ((Nat.min_le_right r (min m l)).trans (Nat.min_le_left m l)))
 Q * (Q.transpose * B) = truncate U sigma V r := validSVD_prefix_projection h r
 theorem literal_residual {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
 {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
 {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
 (a : Fin (min m l)) (ha : 0 < sigma a) (Y : Matrix (Fin m) (Fin l) ℝ)
 (hY : Matrix.rank Y ≤ a.val + 1)
 (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) :
 projectMatrix (singularSubspace U (fun k => sigma a < sigma k)) (B - Y) = 0 :=
 (validSVD_equality_above_span_residual h a ha Y hY heq).2
#assert_trust kernel literal_frame
#assert_trust kernel literal_residual
#print axioms literal_frame
#print axioms literal_residual
end TR04FrameResidualAuthor
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSubspace
#assert_trust kernel NLA.Proofs.TR04.SVD.singularSubspace_le
#assert_trust kernel NLA.Proofs.TR04.SVD.projectMatrix_residual_eq_zero_of_le
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_equality_above_span_residual
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_prefix_coefficients
#assert_trust kernel NLA.Proofs.TR04.SVD.validSVD_prefix_projection
