import NLA.Proofs.TR04.SVDTotal
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace IndependentTR04SVDGeometry
open NLA.Computation.SVDMachine
 theorem literal_machine_SVD_total :
    ∀ (m l : ℕ) (B : Matrix (Fin m) (Fin l) ℝ),
      ∃ (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
        (V : Matrix (Fin l) (Fin l) ℝ), ValidSVD B U sigma V := by
  intro m l B
  exact NLA.Proofs.TR04.SVD.exists_validSVD B
#assert_trust kernel literal_machine_SVD_total
#print axioms literal_machine_SVD_total
#assert_trust kernel NLA.Proofs.TR04.SVD.rightBasis
#assert_trust kernel NLA.Proofs.TR04.SVD.norm_image_rightBasis
#assert_trust kernel NLA.Proofs.TR04.SVD.inner_image_rightBasis
#assert_trust kernel NLA.Proofs.TR04.SVD.image_rightBasis_eq_zero
#assert_trust kernel NLA.Proofs.TR04.SVD.range_finrank_le_domain
#assert_trust kernel NLA.Proofs.TR04.SVD.range_finrank_le_codomain
#assert_trust kernel NLA.Proofs.TR04.SVD.leftVector
#assert_trust kernel NLA.Proofs.TR04.SVD.orthonormal_leftVector_positive
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_leftBasis
#assert_trust kernel NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul
#assert_trust kernel NLA.Proofs.TR04.SVD.sum_fin_truncate
#assert_trust kernel NLA.Proofs.TR04.SVD.exists_validSVD
end IndependentTR04SVDGeometry
