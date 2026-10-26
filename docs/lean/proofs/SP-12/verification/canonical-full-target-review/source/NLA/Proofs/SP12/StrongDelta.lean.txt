import NLA.Proofs.SP12.GramSAP

/-!
# Actual PSD/SAP Strong Delta representations

The completed SP-11 shared-variable proof supplies the actual faithful real
LSS factor. Its nonzero outputs force independent predecessor inputs and hence
SAP. Positivity is the general Gram identity. No external Strong Delta theorem
is assumed, and no chromatic or induced-extension conclusion is claimed here.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Proofs.SP11

namespace NLA.Proofs.SP12

/-- The actual real factor for a positive-order graph has the full Strong Delta
properties, before any induced-vertex extension or chromatic argument. -/
theorem exists_strongDelta_gram_of_pos {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) :
    ∃ (d : ℕ) (R : Matrix (Fin n) (Fin d) ℝ),
      d + NLA.Statements.SP11.MinimumDegree G ≤ n ∧
      NLA.Statements.SP12.HasPattern G (gram R) ∧
      NLA.Statements.SP12.StrongArnold (gram R) := by
  obtain ⟨e, d, hgr, hdim, harity⟩ := exists_orderedGreedy_comap hn G
  obtain ⟨x, hpattern, hnonzero⟩ := exists_faithful_real_evaluation (G.comap e)
    (polynomialLSS (G.comap e) d) (polynomialLSS_nonedge (G.comap e))
    (polynomialLSS_nonzero (G.comap e) hgr harity)
  let R : Matrix (Fin n) (Fin d) ℝ :=
    fun i q => MvPolynomial.eval x (polynomialLSS (G.comap e) d i q)
  have hSAP : NLA.Statements.SP12.StrongArnold (gram R) := by
    apply gram_strongArnold_of_prior_linearIndependent (G.comap e) R hpattern
    intro j
    exact evaluated_polynomialLSS_prior_linearIndependent (G.comap e) x j (hnonzero j)
  refine ⟨d, (fun i => R (e.symm i)), ?_, ?_, ?_⟩
  · rwa [minimumDegree_comap] at hdim
  · exact hasPattern_of_comap G e (gram R) hpattern
  · exact strongArnold_gram_relabel R e.symm hSAP

/-- Strong Delta as a real Gram factor, including the empty auxiliary graph.
The factor's Gram matrix is PSD by gram_nonnegativeQuadraticForm. -/
theorem exists_strongDelta_gram {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ (d : ℕ) (R : Matrix (Fin n) (Fin d) ℝ),
      d + NLA.Statements.SP11.MinimumDegree G ≤ n ∧
      NLA.Statements.SP12.HasPattern G (gram R) ∧
      NLA.Statements.SP12.StrongArnold (gram R) := by
  classical
  by_cases hn : 0 < n
  · exact exists_strongDelta_gram_of_pos hn G
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · simp [NLA.Statements.SP11.MinimumDegree]
    · constructor
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
    · intro X _ _ _ _
      ext i
      exact Fin.elim0 i

#assert_trust kernel exists_strongDelta_gram_of_pos
#assert_trust kernel exists_strongDelta_gram
#print axioms exists_strongDelta_gram

end NLA.Proofs.SP12
