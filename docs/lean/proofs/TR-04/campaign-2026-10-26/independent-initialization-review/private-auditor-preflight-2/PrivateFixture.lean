import LeanCert.Tactic.Verification
set_option leancert.trust "kernel"
namespace IndependentAuditFixture
private theorem hidden : True := True.intro
local instance localProof : NeZero (1 : Nat) := ⟨by decide⟩
def visible : Nat := 1
axiom customAuditOnly : False
private theorem rejected : False := customAuditOnly
end IndependentAuditFixture
