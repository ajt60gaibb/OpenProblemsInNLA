import NLA
import StatementControls
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification
import NLA.Computation.BandIntervalControls
import NLA.Computation.Controls
import NLA.Computation.ExactRealControls
import NLA.Computation.OracleControls
import NLA.Computation.RoundedTreeControls
import NLA.Computation.SVDControls
import NLA.Statements.AA01
import Reviewed.AA01
import NLA.Statements.AV01
import Reviewed.AV01
import NLA.Statements.AV02
import Reviewed.AV02
import NLA.Statements.IE10
import Reviewed.IE10
import NLA.Statements.IE12
import Reviewed.IE12
import NLA.Statements.IE21
import Reviewed.IE21
import NLA.Statements.IE22
import Reviewed.IE22
import NLA.Statements.IE26
import Reviewed.IE26
import NLA.Statements.IV02
import Reviewed.IV02
import NLA.Statements.IV04
import Reviewed.IV04
import NLA.Statements.IV05
import Reviewed.IV05
import NLA.Statements.MD03
import Reviewed.MD03
import NLA.Statements.MD04
import Reviewed.MD04
import NLA.Statements.MD06
import Reviewed.MD06
import NLA.Statements.MF03
import Reviewed.MF03
import NLA.Statements.NM03
import Reviewed.NM03
import NLA.Statements.PF04
import Reviewed.PF04
import NLA.Statements.PF05
import Reviewed.PF05
import NLA.Statements.RA04
import Reviewed.RA04
import NLA.Statements.RA05
import Reviewed.RA05
import NLA.Statements.RA10
import Reviewed.RA10
import NLA.Statements.RA12
import Reviewed.RA12
import NLA.Statements.RA13
import Reviewed.RA13
import NLA.Statements.RA19
import Reviewed.RA19
import NLA.Statements.SP11
import Reviewed.SP11
import NLA.Statements.SP12
import Reviewed.SP12
import NLA.Statements.SP13
import Reviewed.SP13
import NLA.Statements.TR04
import Reviewed.TR04
import NLA.Statements.TR13
import Reviewed.TR13
import NLA.Statements.TR14
import Reviewed.TR14

set_option leancert.trust "kernel"
set_option autoImplicit false
#assert_statement NLA.Statements.AA01.Target
#assert_statement NLA.ReviewedStatements.AA01.Target
#assert_trust kernel NLA.Statements.AA01.Target
#print axioms NLA.Statements.AA01.Target
example : NLA.Statements.AA01.Target = NLA.ReviewedStatements.AA01.Target := by rfl
#assert_statement NLA.Statements.AV01.Target
#assert_statement NLA.ReviewedStatements.AV01.Target
#assert_trust kernel NLA.Statements.AV01.Target
#print axioms NLA.Statements.AV01.Target
example : NLA.Statements.AV01.Target = NLA.ReviewedStatements.AV01.Target := by rfl
#assert_statement NLA.Statements.AV02.Target
#assert_statement NLA.ReviewedStatements.AV02.Target
#assert_trust kernel NLA.Statements.AV02.Target
#print axioms NLA.Statements.AV02.Target
example : NLA.Statements.AV02.Target = NLA.ReviewedStatements.AV02.Target := by rfl
#assert_statement NLA.Statements.IE10.Target
#assert_statement NLA.ReviewedStatements.IE10.Target
#assert_trust kernel NLA.Statements.IE10.Target
#print axioms NLA.Statements.IE10.Target
example : NLA.Statements.IE10.Target = NLA.ReviewedStatements.IE10.Target := by rfl
#assert_statement NLA.Statements.IE12.Target
#assert_statement NLA.ReviewedStatements.IE12.Target
#assert_trust kernel NLA.Statements.IE12.Target
#print axioms NLA.Statements.IE12.Target
example : NLA.Statements.IE12.Target = NLA.ReviewedStatements.IE12.Target := by rfl
#assert_statement NLA.Statements.IE21.Target
#assert_statement NLA.ReviewedStatements.IE21.Target
#assert_trust kernel NLA.Statements.IE21.Target
#print axioms NLA.Statements.IE21.Target
example : NLA.Statements.IE21.Target = NLA.ReviewedStatements.IE21.Target := by rfl
#assert_statement NLA.Statements.IE22.Target
#assert_statement NLA.ReviewedStatements.IE22.Target
#assert_trust kernel NLA.Statements.IE22.Target
#print axioms NLA.Statements.IE22.Target
example : NLA.Statements.IE22.Target = NLA.ReviewedStatements.IE22.Target := by rfl
#assert_statement NLA.Statements.IE26.Target
#assert_statement NLA.ReviewedStatements.IE26.Target
#assert_trust kernel NLA.Statements.IE26.Target
#print axioms NLA.Statements.IE26.Target
example : NLA.Statements.IE26.Target = NLA.ReviewedStatements.IE26.Target := by rfl
#assert_statement NLA.Statements.IV02.Target
#assert_statement NLA.ReviewedStatements.IV02.Target
#assert_trust kernel NLA.Statements.IV02.Target
#print axioms NLA.Statements.IV02.Target
example : NLA.Statements.IV02.Target = NLA.ReviewedStatements.IV02.Target := by rfl
#assert_statement NLA.Statements.IV04.Target
#assert_statement NLA.ReviewedStatements.IV04.Target
#assert_trust kernel NLA.Statements.IV04.Target
#print axioms NLA.Statements.IV04.Target
example : NLA.Statements.IV04.Target = NLA.ReviewedStatements.IV04.Target := by rfl
#assert_statement NLA.Statements.IV05.Target
#assert_statement NLA.ReviewedStatements.IV05.Target
#assert_trust kernel NLA.Statements.IV05.Target
#print axioms NLA.Statements.IV05.Target
example : NLA.Statements.IV05.Target = NLA.ReviewedStatements.IV05.Target := by rfl
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
#assert_statement NLA.Statements.MD06.Target
#assert_statement NLA.ReviewedStatements.MD06.Target
#assert_trust kernel NLA.Statements.MD06.Target
#print axioms NLA.Statements.MD06.Target
example : NLA.Statements.MD06.Target = NLA.ReviewedStatements.MD06.Target := by rfl
#assert_statement NLA.Statements.MF03.Target
#assert_statement NLA.ReviewedStatements.MF03.Target
#assert_trust kernel NLA.Statements.MF03.Target
#print axioms NLA.Statements.MF03.Target
example : NLA.Statements.MF03.Target = NLA.ReviewedStatements.MF03.Target := by rfl
#assert_statement NLA.Statements.NM03.Target
#assert_statement NLA.ReviewedStatements.NM03.Target
#assert_trust kernel NLA.Statements.NM03.Target
#print axioms NLA.Statements.NM03.Target
example : NLA.Statements.NM03.Target = NLA.ReviewedStatements.NM03.Target := by rfl
#assert_statement NLA.Statements.PF04.Target
#assert_statement NLA.ReviewedStatements.PF04.Target
#assert_trust kernel NLA.Statements.PF04.Target
#print axioms NLA.Statements.PF04.Target
example : NLA.Statements.PF04.Target = NLA.ReviewedStatements.PF04.Target := by rfl
#assert_statement NLA.Statements.PF05.Target
#assert_statement NLA.ReviewedStatements.PF05.Target
#assert_trust kernel NLA.Statements.PF05.Target
#print axioms NLA.Statements.PF05.Target
example : NLA.Statements.PF05.Target = NLA.ReviewedStatements.PF05.Target := by rfl
#assert_statement NLA.Statements.RA04.Target
#assert_statement NLA.ReviewedStatements.RA04.Target
#assert_trust kernel NLA.Statements.RA04.Target
#print axioms NLA.Statements.RA04.Target
example : NLA.Statements.RA04.Target = NLA.ReviewedStatements.RA04.Target := by rfl
#assert_statement NLA.Statements.RA05.Target
#assert_statement NLA.ReviewedStatements.RA05.Target
#assert_trust kernel NLA.Statements.RA05.Target
#print axioms NLA.Statements.RA05.Target
example : NLA.Statements.RA05.Target = NLA.ReviewedStatements.RA05.Target := by rfl
#assert_statement NLA.Statements.RA10.Target
#assert_statement NLA.ReviewedStatements.RA10.Target
#assert_trust kernel NLA.Statements.RA10.Target
#print axioms NLA.Statements.RA10.Target
example : NLA.Statements.RA10.Target = NLA.ReviewedStatements.RA10.Target := by rfl
#assert_statement NLA.Statements.RA12.Target
#assert_statement NLA.ReviewedStatements.RA12.Target
#assert_trust kernel NLA.Statements.RA12.Target
#print axioms NLA.Statements.RA12.Target
example : NLA.Statements.RA12.Target = NLA.ReviewedStatements.RA12.Target := by rfl
#assert_statement NLA.Statements.RA13.Target
#assert_statement NLA.ReviewedStatements.RA13.Target
#assert_trust kernel NLA.Statements.RA13.Target
#print axioms NLA.Statements.RA13.Target
example : NLA.Statements.RA13.Target = NLA.ReviewedStatements.RA13.Target := by rfl
#assert_statement NLA.Statements.RA19.Target
#assert_statement NLA.ReviewedStatements.RA19.Target
#assert_trust kernel NLA.Statements.RA19.Target
#print axioms NLA.Statements.RA19.Target
example : NLA.Statements.RA19.Target = NLA.ReviewedStatements.RA19.Target := by rfl
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
#assert_statement NLA.Statements.SP13.Target
#assert_statement NLA.ReviewedStatements.SP13.Target
#assert_trust kernel NLA.Statements.SP13.Target
#print axioms NLA.Statements.SP13.Target
example : NLA.Statements.SP13.Target = NLA.ReviewedStatements.SP13.Target := by rfl
#assert_statement NLA.Statements.TR04.Target
#assert_statement NLA.ReviewedStatements.TR04.Target
#assert_trust kernel NLA.Statements.TR04.Target
#print axioms NLA.Statements.TR04.Target
example : NLA.Statements.TR04.Target = NLA.ReviewedStatements.TR04.Target := by rfl
#assert_statement NLA.Statements.TR13.Target
#assert_statement NLA.ReviewedStatements.TR13.Target
#assert_trust kernel NLA.Statements.TR13.Target
#print axioms NLA.Statements.TR13.Target
example : NLA.Statements.TR13.Target = NLA.ReviewedStatements.TR13.Target := by rfl
#assert_statement NLA.Statements.TR14.Target
#assert_statement NLA.ReviewedStatements.TR14.Target
#assert_trust kernel NLA.Statements.TR14.Target
#print axioms NLA.Statements.TR14.Target
example : NLA.Statements.TR14.Target = NLA.ReviewedStatements.TR14.Target := by rfl
