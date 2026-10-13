import Target
import DualWitness

namespace MD01Scratch

/-- A paper-style positive semidefinite target matrix gives an upper bound
for the exact Lovász theta value used in the formal MD-01 statement. -/
theorem theta_le_of_target_matrix {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (R : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) (ha : 0 < a)
    (hRdiag : ∀ i, R i i = 0)
    (hRnonedge : ∀ i j, ¬ G.Adj i j → R i j = 0)
    (hW : ((1 : Matrix (Fin n) (Fin n) ℝ) +
      a • MD01Dual.signedAdj G + R).PosSemidef) :
    theta G ≤ 1 + 1 / a := by
  unfold theta
  exact MD01Dual.theta_sup_le_of_target_matrix G R a ha hRdiag hRnonedge hW
    (theta_domain_nonempty n hn G)

#print axioms MD01Scratch.theta_le_of_target_matrix

end MD01Scratch
