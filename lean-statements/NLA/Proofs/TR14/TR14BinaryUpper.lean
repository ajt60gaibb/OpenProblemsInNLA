import NLA.Proofs.TR14.TR14BinaryApolarPencil
import NLA.Proofs.TR14.VandermondeReconstruction

/-! Actual binary symmetric upper width in a normalized least-apolar chart.
This is an upper bound, not the arbitrary ordinary lower bound or full Target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

/-- The actual separable apolar polynomial and actual Vandermonde reconstruction
supply the frozen symmetric width D-r+2 for every normalized chart datum. -/
theorem binary_symmetricWidth_of_minimal_monic {m n : ℕ}
    (h : Fin (m * (n - 1) + 1) → ℂ) (hh : h ≠ 0) (g : Polynomial ℂ)
    (hg : g.Monic) (hrPos : 1 ≤ g.natDegree) (hrD : g.natDegree ≤ m * (n - 1))
    (hrHi : g.natDegree ≤ m * (n - 1) / 2 + 1)
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ m * (n - 1), d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ, IsApolar h d hd b → b = 0) :
    NLA.Statements.TR14.SymmetricWidth (NLA.Statements.TR14.Hankel h)
      (m * (n - 1) - g.natDegree + 2) := by
  obtain ⟨P, hm, hdeg, hs, hr⟩ :=
    binary_separable_apolar_polynomial h hh g hg hrPos hrD hrHi hAp hmin
  have hPD : P.natDegree ≤ m * (n - 1) + 1 := by rw [hdeg]; omega
  have hw := symmetricWidth_of_monic_separable_recurrence h P hm hs hPD hr
  simpa only [hdeg] using hw

#assert_trust kernel binary_symmetricWidth_of_minimal_monic
#print axioms binary_symmetricWidth_of_minimal_monic

end NLA.Proofs.TR14
