import NLA.Proofs.SP11.DoubleRootGarden
import NLA.Proofs.SP11.MonomialProducts

/-!
# Read a unique nonzero coefficient of the actual Gram polynomial

The hypotheses concern exactly the finite paired-coloring sum already proved
equal to polynomialGram. Zero-sign colorings may share the chosen exponent.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11

theorem polynomialGram_coeff_eq_of_unique {n d : ℕ}
    (G : SimpleGraph (Fin n)) (i j : Fin n)
    (best : GardenTree.DoubleColoring d (lssGarden G i) (lssGarden G j))
    (hunique : ∀ actual : GardenTree.DoubleColoring d (lssGarden G i) (lssGarden G j),
      GardenTree.doubleColoringSign ℝ (lssGarden G i) (lssGarden G j) actual ≠ 0 →
      GardenTree.doubleColoringExponent (lssGarden G i) (lssGarden G j) actual =
        GardenTree.doubleColoringExponent (lssGarden G i) (lssGarden G j) best → actual = best) :
    MvPolynomial.coeff (GardenTree.doubleColoringExponent (lssGarden G i) (lssGarden G j) best)
      (polynomialGram (polynomialLSS G d) i j) =
      GardenTree.doubleColoringSign ℝ (lssGarden G i) (lssGarden G j) best := by
  classical
  rw [polynomialGram_eq_sum_signedGardenMonomial]
  exact coeff_sum_monomial_of_unique Finset.univ _ _ best (Finset.mem_univ _)
    (fun actual _ => hunique actual)

theorem polynomialGram_ne_zero_of_unique {n d : ℕ}
    (G : SimpleGraph (Fin n)) (i j : Fin n)
    (best : GardenTree.DoubleColoring d (lssGarden G i) (lssGarden G j))
    (hbest : GardenTree.doubleColoringSign ℝ (lssGarden G i) (lssGarden G j) best ≠ 0)
    (hunique : ∀ actual : GardenTree.DoubleColoring d (lssGarden G i) (lssGarden G j),
      GardenTree.doubleColoringSign ℝ (lssGarden G i) (lssGarden G j) actual ≠ 0 →
      GardenTree.doubleColoringExponent (lssGarden G i) (lssGarden G j) actual =
        GardenTree.doubleColoringExponent (lssGarden G i) (lssGarden G j) best → actual = best) :
    polynomialGram (polynomialLSS G d) i j ≠ 0 := by
  intro hz
  have hc := polynomialGram_coeff_eq_of_unique G i j best hunique
  rw [hz, MvPolynomial.coeff_zero] at hc
  exact hbest hc.symm

#assert_trust kernel polynomialGram_coeff_eq_of_unique
#assert_trust kernel polynomialGram_ne_zero_of_unique
#print axioms polynomialGram_ne_zero_of_unique

end NLA.Proofs.SP11
