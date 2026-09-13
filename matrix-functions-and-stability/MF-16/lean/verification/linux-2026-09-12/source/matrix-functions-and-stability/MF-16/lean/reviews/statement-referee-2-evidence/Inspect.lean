/- Independent statement referee 2. Machine diagnostics are not kernel certificates. -/
import Challenge
import LeanCert.Tactic.Verification
set_option autoImplicit false
set_option pp.universes false
open scoped ComplexOrder
namespace NLA.MF16.RootStatementReview
open LeanCert.Core LeanCert.Engine NLA.MF16
set_option pp.all true in
#print NLA.MF16.WordUniquenessConjecture
#print NLA.MF16.SymmetricWord
set_option pp.all true in
#print NLA.MF16.evalWord
#print NLA.MF16.complexify
#print Matrix.PosDef
#print LeanCert.Engine.FinBoxMem
#print LeanCert.Engine.SystemZero
#check LeanCert.Engine.krawczykCheck_sound
#check LeanCert.Engine.fixedPoint_iff_systemZero
#check Matrix.aeval_self_charpoly
def ratJson (q : ℚ) : Lean.Json := .str (toString q.num ++ "/" ++ toString q.den)
def expressionJson : Expr → Lean.Json
  | .const q => .arr #[.str "constant", ratJson q]
  | .var i => .arr #[.str "variable", .num i]
  | .add a b => .arr #[.str "add", expressionJson a, expressionJson b]
  | .mul a b => .arr #[.str "multiply", expressionJson a, expressionJson b]
  | .neg a => .arr #[.str "negate", expressionJson a]
  | _ => .str "UNSUPPORTED"
def intervalJson (i : IntervalRat) : Lean.Json := .arr #[ratJson i.lo, ratJson i.hi]
#eval IO.println ("ROOT_AST=" ++ (Lean.Json.arr ((List.ofFn polynomialSystem).map expressionJson).toArray).compress)
#eval IO.println ("ROOT_CENTER=" ++ (Lean.Json.arr ((List.ofFn rootCenter).map ratJson).toArray).compress)
#eval IO.println ("ROOT_BOX=" ++ (Lean.Json.arr ((List.ofFn rootBox).map intervalJson).toArray).compress)
#eval IO.println ("ROOT_C=" ++ (Lean.Json.arr (List.ofFn fun i => Lean.Json.arr ((List.ofFn (rootCertificate.preconditioner i)).map ratJson).toArray).toArray).compress)
#eval IO.println ("ROOT_J=" ++ (Lean.Json.arr (List.ofFn fun i => Lean.Json.arr ((List.ofFn (intervalJacobian polynomialSystem rootBox {} i)).map intervalJson).toArray).toArray).compress)
#eval IO.println ("ROOT_IMAGE=" ++ (Lean.Json.arr ((List.ofFn (newtonImageEnclosure polynomialSystem rootBox rootCenter rootCertificate.preconditioner {})).map intervalJson).toArray).compress)
#eval IO.println ("ROOT_Q=" ++ (ratJson contractionBound).compress)
#eval IO.println ("ROOT_CHECK=" ++ toString (krawczykCheck polynomialSystem rootBox rootCertificate {}))
#eval IO.println ("ROOT_DET=" ++ (ratJson rootCertificate.preconditioner.det).compress)
#eval IO.println ("ROOT_RADIUS=" ++ (ratJson (boxRadius rootBox rootCenter)).compress)
#assert_trust kernel LeanCert.Engine.krawczykCheck_sound
#print axioms LeanCert.Engine.krawczykCheck_sound
#check NLA.MF16.word_semantics
#check NLA.MF16.source_data
#check NLA.MF16.twelfth_power_reduction
#check NLA.MF16.polynomial_word_equivalence
#check NLA.MF16.krawczyk_certificate
#check NLA.MF16.certified_root
#check NLA.MF16.root_to_matrix
#check NLA.MF16.counterexample
#check NLA.MF16.not_wordUniquenessConjecture
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
#print axioms NLA.MF16.not_wordUniquenessConjecture
end NLA.MF16.RootStatementReview
