import NLA.Proofs.SP11.PolynomialLSS
import NLA.Proofs.SP11.GreedyOrdering
import Reviewed.SP11

set_option autoImplicit false
set_option leancert.trust "kernel"

example : NLA.Statements.SP11.Target = NLA.ReviewedStatements.SP11.Target := rfl

#check NLA.Proofs.SP11.alternatingContraction_orthogonal
#check NLA.Proofs.SP11.polynomialAlternatingForm_apply
#check NLA.Proofs.SP11.uniformLSS_orthogonal_nonedge
#check NLA.Proofs.SP11.exists_pattern_matrix_of_polynomialLSS_nonzero
#check NLA.Proofs.SP11.target_of_polynomial_representations
#assert_trust kernel NLA.Proofs.SP11.alternatingContraction_orthogonal
#assert_trust kernel NLA.Proofs.SP11.polynomialAlternatingForm_apply
#assert_trust kernel NLA.Proofs.SP11.uniformLSS_orthogonal_nonedge
#assert_trust kernel NLA.Proofs.SP11.exists_pattern_matrix_of_polynomialLSS_nonzero
#assert_trust kernel NLA.Proofs.SP11.target_of_polynomial_representations
#print axioms NLA.Proofs.SP11.alternatingContraction_orthogonal
#print axioms NLA.Proofs.SP11.polynomialAlternatingForm_apply
#print axioms NLA.Proofs.SP11.uniformLSS_orthogonal_nonedge
#print axioms NLA.Proofs.SP11.exists_pattern_matrix_of_polynomialLSS_nonzero
#print axioms NLA.Proofs.SP11.target_of_polynomial_representations
