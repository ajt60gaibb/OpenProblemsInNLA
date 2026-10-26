import LeanCert.Tactic.Verification
namespace IndependentIdentityFixture
private theorem same : True := True.intro
private theorem denied : True := True.intro
local instance localProof : NeZero (1 : Nat) := ⟨by decide⟩
def visible : Nat := 1
end IndependentIdentityFixture
