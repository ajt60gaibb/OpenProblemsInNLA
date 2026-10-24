import NLA.Proofs.TR04.SVDTotal
set_option autoImplicit false
set_option leancert.trust "kernel"
theorem exact_rectangular_svd {m l : ℕ} (B : Matrix (Fin m) (Fin l) ℝ) :
 ∃ U sigma V, NLA.Computation.SVDMachine.ValidSVD B U sigma V :=
 NLA.Proofs.TR04.SVD.exists_validSVD B
#assert_trust kernel exact_rectangular_svd
#print axioms exact_rectangular_svd
