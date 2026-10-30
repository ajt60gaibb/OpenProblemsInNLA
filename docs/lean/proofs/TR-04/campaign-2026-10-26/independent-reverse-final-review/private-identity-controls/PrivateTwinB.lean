import LeanCert.Tactic.Verification
namespace IndependentIdentityFixture
private theorem same : True := True.intro
axiom hiddenControlOnly : False
private theorem denied : False := hiddenControlOnly
end IndependentIdentityFixture
