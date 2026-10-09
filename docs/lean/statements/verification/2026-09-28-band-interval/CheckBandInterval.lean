import NLA.Statements.IV02
import Reviewed.IV02
import NLA.Statements.IV04
import Reviewed.IV04

theorem checkIV02 : NLA.Statements.IV02.Target = NLA.ReviewedStatements.IV02.Target := rfl
#print axioms checkIV02
theorem checkIV04 : NLA.Statements.IV04.Target = NLA.ReviewedStatements.IV04.Target := rfl
#print axioms checkIV04
