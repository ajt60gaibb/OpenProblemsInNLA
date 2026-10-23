import NLA.Proofs.TR14.LocalCRTFourierWidth
import NLA.Proofs.TR14.GL2WidthTransport

/-! TR-14: transport the exact local CRT/Fourier symmetric-width witness
from a normalized chart back to the original Hankel tensor. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open NLA.Statements.TR14 Polynomial
open scoped BigOperators Polynomial

noncomputable section

theorem chart_localCRTFourier_symmetricWidth {m n : ℕ}
    (hm : 3 ≤ m) (hn : 2 ≤ n)
    (h : Fin (m * (n - 1) + 1) → ℂ) (z : ℂ)
    (g : Polynomial ℂ) (hg : g.Monic)
    (hrPos : 1 ≤ g.natDegree)
    (hrD : g.natDegree ≤ m * (n - 1))
    (hhTrans : transformedMoments z h ≠ 0)
    (hAp : IsApolar (transformedMoments z h) g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ m * (n - 1),
      d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ,
        IsApolar (transformedMoments z h) d hd b → b = 0) :
    NLA.Statements.TR14.SymmetricWidth
      (NLA.Statements.TR14.Hankel h)
      ((m - 1) * g.natDegree -
        (m - 2) * (localRootSupport g).card) := by
  cases n with
  | zero => omega
  | succ q =>
    let R := (m - 1) * g.natDegree - (m - 2) * (localRootSupport g).card
    have hlocal : SymmetricWidth
        (Hankel (m := m) (n := q + 1) (transformedMoments z h)) R :=
      localCRTFourier_symmetricWidth_of_minimal hm hn
        (transformedMoments z h) hhTrans g hg hrPos hrD hAp hmin
    exact chart_symmetricWidth_reverse z m q R h hlocal

#assert_trust kernel chart_localCRTFourier_symmetricWidth
#print axioms chart_localCRTFourier_symmetricWidth

end
end NLA.Proofs.TR14
