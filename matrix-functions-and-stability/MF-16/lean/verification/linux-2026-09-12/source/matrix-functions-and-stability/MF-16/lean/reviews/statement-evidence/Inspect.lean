/- Statement-only actual definitions and checker observation; no solution theorem. -/
import NLA.MF16.Definitions
import LeanCert.Tactic.Verification
set_option pp.universes false
open scoped ComplexOrder
namespace NLA.MF16.StatementInspection
open NLA.MF16 LeanCert.Core LeanCert.Engine
#print NLA.MF16.WordUniquenessConjecture
#print NLA.MF16.SymmetricWord
#print NLA.MF16.evalWord
#print NLA.MF16.symmetricMatrix
#print NLA.MF16.complexify
#print Matrix.PosDef
#print NLA.MF16.linearCoefficient
#print NLA.MF16.identityCoefficient
#print NLA.MF16.polynomialSystem
#print NLA.MF16.rootCenter
#print NLA.MF16.rootBox
#print NLA.MF16.rootCertificate
#print LeanCert.Engine.krawczykCheck
#check LeanCert.Engine.krawczykCheck_sound
#check LeanCert.Engine.jacobianAt_mem_intervalJacobian
#check LeanCert.Engine.contraction_unique_fixedPoint_in_finBox
#check Matrix.aeval_self_charpoly
#check Matrix.posDef_iff_dotProduct_mulVec
/-- Diagnostic serialization of the actual checked AST; no mathematical theorem. -/
def exprTokens : Expr → List String
  | .const q => ["c:" ++ toString q.num ++ "/" ++ toString q.den]
  | .var i => ["v:" ++ toString i]
  | .add a b => ["a"] ++ exprTokens a ++ exprTokens b
  | .mul a b => ["m"] ++ exprTokens a ++ exprTokens b
  | .neg a => ["n"] ++ exprTokens a
  | _ => ["UNSUPPORTED"]
def ratData (q : ℚ) : String := toString q.num ++ "/" ++ toString q.den
#eval IO.println ("POLYNOMIAL_AST=" ++ String.intercalate "|"
  ((List.ofFn polynomialSystem).map fun e => String.intercalate "," (exprTokens e)))
#eval IO.println ("CENTER=" ++ String.intercalate "," ((List.ofFn rootCenter).map ratData))
#eval IO.println ("BOX=" ++ String.intercalate ","
  ((List.ofFn fun i => [ratData (rootBox i).lo, ratData (rootBox i).hi]).flatten))
#eval IO.println ("PRECONDITIONER=" ++ String.intercalate ","
  ((List.ofFn fun i => (List.ofFn (rootCertificate.preconditioner i)).map ratData).flatten))
#eval IO.println ("CONTRACTION_BOUND=" ++ ratData contractionBound)
#eval witnessWord
#eval witnessWord.length
#eval witnessWord.count Letter.X
#eval witnessWord.count Letter.B
#eval krawczykCheck polynomialSystem rootBox rootCertificate {}
#eval contractionBound < (27/1000 : ℚ)
#eval rootCertificate.preconditioner.det
#eval boxRadius rootBox rootCenter
#assert_trust kernel LeanCert.Engine.krawczykCheck_sound
#print axioms LeanCert.Engine.krawczykCheck_sound
#assert_trust kernel WordUniquenessConjecture
#assert_trust kernel SymmetricWord
#assert_trust kernel evalWord
#assert_trust kernel symmetricMatrix
#assert_trust kernel complexify
#assert_trust kernel polynomialSystem
#assert_trust kernel rootBox
#assert_trust kernel rootCertificate
#assert_trust kernel contractionBound
#print axioms NLA.MF16.WordUniquenessConjecture
#print axioms NLA.MF16.SymmetricWord
#print axioms NLA.MF16.evalWord
#print axioms NLA.MF16.symmetricMatrix
#print axioms NLA.MF16.complexify
#print axioms NLA.MF16.polynomialSystem
#print axioms NLA.MF16.rootBox
#print axioms NLA.MF16.rootCertificate
#print axioms NLA.MF16.contractionBound
end NLA.MF16.StatementInspection
