import NLA.Proofs.SP11.DiagonalUniqueness
import NLA.Proofs.SP11.EdgeUniqueness
import NLA.Proofs.SP11.GramCoefficient

/-!
# The complete unrestricted real symmetric delta target

The exact shared-variable Gram expansion has a unique nonzero canonical
coefficient at every edge and diagonal. One real evaluation preserves all
required entries. Greedy relabeling and the Gram rank bound then prove the
unchanged all-graph target. No external delta theorem is assumed.

Mathematical construction: H. Tracy Hall, The Delta Theorem,
arXiv:2601.01211v1, Sections 3–5. Formalization: OpenAI Codex AI agents.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11

theorem polynomialLSS_nonzero_ordered {n d : ℕ} (G : SimpleGraph (Fin n))
    (hgr : OrderedGreedy G) (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d)
    (i j : Fin n) (hij : i ≤ j) (hcase : i = j ∨ G.Adj i j) :
    polynomialGram (polynomialLSS G d) i j ≠ 0 := by
  apply polynomialGram_ne_zero_of_unique G i j (canonicalPair G hd i j)
    (canonicalPair_sign_ne_zero G hgr hd i j hij)
  intro actual ha he
  by_cases heq : i = j
  · subst j
    exact canonicalPair_diagonal_unique G hgr hd i actual ha he
  · have hadj : G.Adj i j := hcase.resolve_left heq
    exact canonicalPair_edge_unique G hgr hd i j (lt_of_le_of_ne hij heq) hadj actual ha he

theorem polynomialLSS_nonzero {n d : ℕ} (G : SimpleGraph (Fin n))
    (hgr : OrderedGreedy G) (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d)
    (i j : Fin n) (hcase : i = j ∨ G.Adj i j) :
    polynomialGram (polynomialLSS G d) i j ≠ 0 := by
  by_cases hij : i ≤ j
  · exact polynomialLSS_nonzero_ordered G hgr hd i j hij hcase
  · have hji : j ≤ i := (lt_of_not_ge hij).le
    have hcase' : j = i ∨ G.Adj j i := hcase.imp Eq.symm (fun h => h.symm)
    have hn := polynomialLSS_nonzero_ordered G hgr hd j i hji hcase'
    have hs : polynomialGram (polynomialLSS G d) j i =
        polynomialGram (polynomialLSS G d) i j := by
      unfold polynomialGram
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    rwa [hs] at hn

/-- Every positive-order finite simple graph admits the exact real symmetric
pattern with nullity at least its minimum degree, as originally asked. -/
theorem target : NLA.Statements.SP11.Target := by
  apply target_of_orderedGreedy_polynomialLSS_nonzero
  intro n _hn G hgr d hd i j hcase
  exact polynomialLSS_nonzero G hgr hd i j hcase

#assert_trust kernel polynomialLSS_nonzero_ordered
#assert_trust kernel polynomialLSS_nonzero
#assert_trust kernel target
#print axioms target

end NLA.Proofs.SP11
