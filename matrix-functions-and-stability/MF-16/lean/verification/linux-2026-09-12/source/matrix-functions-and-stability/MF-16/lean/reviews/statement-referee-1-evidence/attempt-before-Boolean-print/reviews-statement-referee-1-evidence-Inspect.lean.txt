/- Independent statement referee 1. Diagnostic computation is not a proof of
the candidate Boolean certificate. No admitted Challenge theorem is consumed. -/
import Challenge
import LeanCert.Tactic.Verification

set_option pp.universes false
open scoped ComplexOrder
open NLA.MF16 LeanCert.Core LeanCert.Engine

set_option pp.all true in
#print NLA.MF16.WordUniquenessConjecture
set_option pp.all true in
#print NLA.MF16.evalWord
set_option pp.all true in
#print NLA.MF16.complexify
set_option pp.all true in
#print Matrix.PosDef
#print NLA.MF16.SymmetricWord
#print NLA.MF16.symmetricMatrix
#print NLA.MF16.linearCoefficient
#print NLA.MF16.identityCoefficient
#print NLA.MF16.rootBox
#print NLA.MF16.rootCertificate
#print LeanCert.Engine.SystemZero
#print LeanCert.Engine.FinBoxMem
#print LeanCert.Engine.krawczykCheck
#check LeanCert.Engine.krawczykCheck_sound
#check LeanCert.Engine.jacobianAt_mem_intervalJacobian
#check LeanCert.Engine.contraction_unique_fixedPoint_in_finBox
#check Matrix.aeval_self_charpoly
#check Matrix.posDef_iff_dotProduct_mulVec
#check NLA.MF16.word_semantics
#check NLA.MF16.source_data
#check NLA.MF16.twelfth_power_reduction
#check NLA.MF16.polynomial_word_equivalence
#check NLA.MF16.krawczyk_certificate
#check NLA.MF16.certified_root
#check NLA.MF16.root_to_matrix
#check NLA.MF16.counterexample
#check NLA.MF16.not_wordUniquenessConjecture

namespace NLA.MF16.IndependentStatementReferee1
/- Serialize the elaborated AST for a separately implemented exact evaluator.
This tiny diagnostic follows the same generic prefix representation as the
author inspector; it imports no author diagnostic module. -/
def tokens : Expr → List String
  | .const q => ["c:" ++ toString q.num ++ "/" ++ toString q.den]
  | .var i => ["v:" ++ toString i]
  | .add a b => "a" :: (tokens a ++ tokens b)
  | .mul a b => "m" :: (tokens a ++ tokens b)
  | .neg a => "n" :: tokens a
  | _ => ["UNSUPPORTED"]
def ratio (q : ℚ) : String := toString q.num ++ "/" ++ toString q.den
#eval IO.println ("AST=" ++ String.intercalate "|"
  ((List.ofFn polynomialSystem).map (String.intercalate "," ∘ tokens)))
#eval IO.println ("CENTER=" ++ String.intercalate "," ((List.ofFn rootCenter).map ratio))
#eval IO.println ("BOX=" ++ String.intercalate ","
  ((List.ofFn fun i => [ratio (rootBox i).lo, ratio (rootBox i).hi]).flatten))
#eval IO.println ("C=" ++ String.intercalate ","
  ((List.ofFn fun i => (List.ofFn (rootCertificate.preconditioner i)).map ratio).flatten))
#eval IO.println ("Q=" ++ ratio contractionBound)
#eval IO.println ("DET=" ++ ratio rootCertificate.preconditioner.det)
#eval IO.println ("RADIUS=" ++ ratio (boxRadius rootBox rootCenter))
#eval IO.println ("CHECK=" ++ toString (krawczykCheck polynomialSystem rootBox rootCertificate {}))
#eval IO.println ("BOUND=" ++ toString (contractionBound < (27/1000 : ℚ)))

#assert_trust kernel LeanCert.Engine.krawczykCheck_sound
#print axioms LeanCert.Engine.krawczykCheck_sound
#assert_trust kernel NLA.MF16.WordUniquenessConjecture
#print axioms NLA.MF16.WordUniquenessConjecture
#assert_trust kernel NLA.MF16.SymmetricWord
#print axioms NLA.MF16.SymmetricWord
#assert_trust kernel NLA.MF16.evalWord
#print axioms NLA.MF16.evalWord
#assert_trust kernel NLA.MF16.symmetricMatrix
#print axioms NLA.MF16.symmetricMatrix
#assert_trust kernel NLA.MF16.complexify
#print axioms NLA.MF16.complexify
#assert_trust kernel NLA.MF16.polynomialSystem
#print axioms NLA.MF16.polynomialSystem
#assert_trust kernel NLA.MF16.rootBox
#print axioms NLA.MF16.rootBox
#assert_trust kernel NLA.MF16.rootCertificate
#print axioms NLA.MF16.rootCertificate
#assert_trust kernel NLA.MF16.contractionBound
#print axioms NLA.MF16.contractionBound
end NLA.MF16.IndependentStatementReferee1
