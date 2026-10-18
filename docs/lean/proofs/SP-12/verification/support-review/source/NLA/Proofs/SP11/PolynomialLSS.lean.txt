import NLA.Proofs.SP11.UniformLSS
import NLA.Proofs.SP11.AlternatingPolynomial
import NLA.Proofs.SP11.PolynomialFaithfulness

/-!
# The actual shared-variable polynomial LSS construction

Every vertex has one family of indeterminates, indexed by increasing coordinate
subsets of its required alternating-tensor arity. Every recursive occurrence
of that vertex uses those same indeterminates. Thus this construction retains
the possible cancellations addressed by Hall's unique-monomial lemma.

The nonedge identity is proved here. Nonvanishing at edges and diagonals is
still an explicit missing theorem; it is not encoded into any definition.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11

/-- Distinct tensor coefficients are independent variables; recursive
occurrences of a vertex share its coefficient family. -/
abbrev LSSVariable {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) :=
  (j : Fin n) × CoordinateSubset d ((priorNonneighbors G j).length + 1)

/-- Concrete determinant-minor forms for the actual polynomial coefficient ring. -/
noncomputable def universalVertexForms {n d : ℕ} (G : SimpleGraph (Fin n)) :
    VertexForms G (MvPolynomial (LSSVariable G d) ℝ) d :=
  fun j => polynomialAlternatingForm (fun s => Sigma.mk j s)

/-- Rows are the recursive polynomial vectors, in the original fixed vertex order. -/
noncomputable def polynomialLSS {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) :
    Matrix (Fin n) (Fin d) (MvPolynomial (LSSVariable G d) ℝ) :=
  uniformLSS G (universalVertexForms G)

/-- Every distinct graph nonedge is an identically zero Gram polynomial. -/
theorem polynomialLSS_nonedge {n d : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : i ≠ j) (hnot : ¬ G.Adj i j) :
    polynomialGram (polynomialLSS G d) i j = 0 :=
  uniformLSS_orthogonal_nonedge G (universalVertexForms G) i j hij hnot

/-- Once non-cancellation is proved for this exact shared-variable construction,
its specialization gives an actual faithful real matrix of the required rank.
The premise is not discharged in this module. -/
theorem exists_pattern_matrix_of_polynomialLSS_nonzero {n d : ℕ}
    (G : SimpleGraph (Fin n))
    (hd : d + NLA.Statements.SP11.MinimumDegree G ≤ n)
    (hnonzero : ∀ i j, i = j ∨ G.Adj i j →
      polynomialGram (polynomialLSS G d) i j ≠ 0) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      NLA.Statements.SP11.HasPattern G A ∧
      NLA.Statements.SP11.MinimumDegree G ≤ n - A.rank := by
  obtain ⟨x, hpattern, _⟩ := exists_faithful_real_evaluation G (polynomialLSS G d)
    (polynomialLSS_nonedge G) hnonzero
  exact ⟨gram (fun i k => MvPolynomial.eval x (polynomialLSS G d i k)),
    hpattern, minDegree_le_gram_nullity G _ hd⟩

#assert_trust kernel polynomialLSS_nonedge
#assert_trust kernel exists_pattern_matrix_of_polynomialLSS_nonzero
#print axioms polynomialLSS_nonedge
#print axioms exists_pattern_matrix_of_polynomialLSS_nonzero

end NLA.Proofs.SP11
