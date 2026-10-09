import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification
import NLA.Statements.MD03
import Reviewed.MD03
import NLA.Statements.MD04
import Reviewed.MD04
import NLA.Statements.PF04
import Reviewed.PF04
import NLA.Statements.SP11
import Reviewed.SP11
import NLA.Statements.SP12
import Reviewed.SP12
import NLA.Statements.TR14
import Reviewed.TR14

set_option leancert.trust "kernel"
set_option autoImplicit false
#assert_statement NLA.Statements.MD03.Target
#assert_statement NLA.ReviewedStatements.MD03.Target
#assert_trust kernel NLA.Statements.MD03.Target
#print axioms NLA.Statements.MD03.Target
example : NLA.Statements.MD03.Target = NLA.ReviewedStatements.MD03.Target := by rfl
#assert_statement NLA.Statements.MD04.Target
#assert_statement NLA.ReviewedStatements.MD04.Target
#assert_trust kernel NLA.Statements.MD04.Target
#print axioms NLA.Statements.MD04.Target
example : NLA.Statements.MD04.Target = NLA.ReviewedStatements.MD04.Target := by rfl
#assert_statement NLA.Statements.PF04.Target
#assert_statement NLA.ReviewedStatements.PF04.Target
#assert_trust kernel NLA.Statements.PF04.Target
#print axioms NLA.Statements.PF04.Target
example : NLA.Statements.PF04.Target = NLA.ReviewedStatements.PF04.Target := by rfl
#assert_statement NLA.Statements.SP11.Target
#assert_statement NLA.ReviewedStatements.SP11.Target
#assert_trust kernel NLA.Statements.SP11.Target
#print axioms NLA.Statements.SP11.Target
example : NLA.Statements.SP11.Target = NLA.ReviewedStatements.SP11.Target := by rfl
#assert_statement NLA.Statements.SP12.Target
#assert_statement NLA.ReviewedStatements.SP12.Target
#assert_trust kernel NLA.Statements.SP12.Target
#print axioms NLA.Statements.SP12.Target
example : NLA.Statements.SP12.Target = NLA.ReviewedStatements.SP12.Target := by rfl
#assert_statement NLA.Statements.TR14.Target
#assert_statement NLA.ReviewedStatements.TR14.Target
#assert_trust kernel NLA.Statements.TR14.Target
#print axioms NLA.Statements.TR14.Target
example : NLA.Statements.TR14.Target = NLA.ReviewedStatements.TR14.Target := by rfl
