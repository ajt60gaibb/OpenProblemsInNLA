import NLA.Statements.Infrastructure
import NLA.Computation.ExactRealControls
import NLA.Computation.OracleControls

namespace StatementControls

def valid : Prop := ∀ n : Nat, n + 0 = n
#assert_statement valid

axiom unproved : Prop
/-- error: statement target must be a definition -/
#guard_msgs in
#assert_statement unproved

def wrongType : Nat := 0
/-- error: statement target must have the closed type Prop -/
#guard_msgs in
#assert_statement wrongType

def parameterized (n : Nat) : Prop := n = n
/-- error: statement target must have the closed type Prop -/
#guard_msgs in
#assert_statement parameterized

def customDependent : Prop := unproved
/-- error: statement target has a forbidden axiom: StatementControls.unproved -/
#guard_msgs in
#assert_statement customDependent

/-- warning: declaration uses `sorry` -/
#guard_msgs in
def sorryDependent : Prop := by sorry
/-- error: statement target has a forbidden axiom: sorryAx -/
#guard_msgs in
#assert_statement sorryDependent

theorem nativeProof : (List.range 37).reverse.length = 37 := by native_decide
def nativeDependent : Prop := nativeProof = nativeProof
/-- error: statement target has a forbidden axiom: StatementControls.nativeProof._native.native_decide.ax_1_1 -/
#guard_msgs in
#assert_statement nativeDependent

end StatementControls
