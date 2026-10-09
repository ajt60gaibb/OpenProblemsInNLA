import NLA.Statements.AV01
import Reviewed.AV01
import NLA.Statements.IV05
import Reviewed.IV05

theorem checkAV01 : NLA.Statements.AV01.Target = NLA.ReviewedStatements.AV01.Target := rfl
#print axioms checkAV01
theorem checkIV05 : NLA.Statements.IV05.Target = NLA.ReviewedStatements.IV05.Target := rfl
#print axioms checkIV05
