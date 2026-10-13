import NLA.MD03.Proof
import NLA.MD04.Reduction

set_option leancert.trust "kernel"

/-- The complete, unchanged reviewed MD-04 target follows from MD-03. -/
theorem NLA.MD04.target : NLA.Statements.MD04.Target :=
  NLA.MD04.of_komlos NLA.MD03.target

#assert_trust kernel NLA.MD04.target
#print axioms NLA.MD04.target
