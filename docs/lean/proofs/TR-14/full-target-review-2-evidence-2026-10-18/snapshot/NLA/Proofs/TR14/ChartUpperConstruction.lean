import NLA.Proofs.TR14.GL2ChartNormalize
import NLA.Proofs.TR14.ChartLocalFourierWidth
import NLA.Proofs.TR14.TR14BinaryUpper

/-! Actual normalization and the two complementary symmetric upper widths.
The same chosen affine modulus is used throughout; no projective support
formula or unrestricted ordinary lower bound is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open NLA.Statements.TR14

/-- Choose and normalize an actual least apolar form, retaining every exact
minimality condition needed by the binary and local constructions. -/
theorem exists_normalized_minimal_chart {D : ℕ}
    (h : Fin (D + 1) → ℂ) (hD : 1 ≤ D) (hh : h ≠ 0) :
    ∃ (z : ℂ) (g : Polynomial ℂ) (hrD : g.natDegree ≤ D),
      g.Monic ∧ 1 ≤ g.natDegree ∧ g.natDegree ≤ D / 2 + 1 ∧
      transformedMoments z h ≠ 0 ∧
      IsApolar (transformedMoments z h) g.natDegree hrD
        (fun i : Fin (g.natDegree + 1) => g.coeff i.val) ∧
      (∀ d : ℕ, ∀ hd : d ≤ D, d < g.natDegree →
        ∀ b : Fin (d + 1) → ℂ,
          IsApolar (transformedMoments z h) d hd b → b = 0) := by
  obtain ⟨r, hrD, hrLo, hrHi, ⟨a, ha, hap⟩, hmin⟩ := minimal_apolar_exists h hD hh
  obtain ⟨z, b, g, htrans, _hb, hbAp, _hbTop, hg, hdeg, hcoeff, hmin'⟩ :=
    normalize_chosen_minimal_apolar h hD hh hrD hrLo hrHi a ha hap hmin
  subst r
  refine ⟨z, g, hrD, hg, hrLo, hrHi, htrans, ?_, hmin'⟩
  have heq : (fun i : Fin (g.natDegree + 1) => g.coeff i.val) = b := funext hcoeff
  rw [heq]
  exact hbAp

/-- Both actual symmetric widths hold in the original coordinates for the
same normalized least-apolar chart data. Their minimum can later be compared
with an independently proved arbitrary ordinary lower bound. -/
theorem exists_chart_two_symmetricWidths {m n : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n)
    (h : Fin (m * (n - 1) + 1) → ℂ) (hh : h ≠ 0) :
    ∃ (z : ℂ) (g : Polynomial ℂ) (hrD : g.natDegree ≤ m * (n - 1)),
      g.Monic ∧ 1 ≤ g.natDegree ∧ g.natDegree ≤ m * (n - 1) / 2 + 1 ∧
      transformedMoments z h ≠ 0 ∧
      IsApolar (transformedMoments z h) g.natDegree hrD
        (fun i : Fin (g.natDegree + 1) => g.coeff i.val) ∧
      (∀ d : ℕ, ∀ hd : d ≤ m * (n - 1), d < g.natDegree →
        ∀ b : Fin (d + 1) → ℂ,
          IsApolar (transformedMoments z h) d hd b → b = 0) ∧
      SymmetricWidth (Hankel h) (m * (n - 1) - g.natDegree + 2) ∧
      SymmetricWidth (Hankel h)
        ((m - 1) * g.natDegree - (m - 2) * (localRootSupport g).card) := by
  cases n with
  | zero => omega
  | succ q =>
    have hD : 1 ≤ m * q := by
      have hq : 1 ≤ q := by omega
      nlinarith
    obtain ⟨z, g, hrD, hg, hrLo, hrHi, htrans, hAp, hmin⟩ :=
      exists_normalized_minimal_chart h hD hh
    have hbin := binary_symmetricWidth_of_minimal_monic
      (transformedMoments z h) htrans g hg hrLo hrD hrHi hAp hmin
    have hbinBack := chart_symmetricWidth_reverse z m q
      (m * q - g.natDegree + 2) h hbin
    have hlocal := chart_localCRTFourier_symmetricWidth hm hn h z g hg hrLo hrD
      htrans hAp hmin
    exact ⟨z, g, hrD, hg, hrLo, hrHi, htrans, hAp, hmin, hbinBack, hlocal⟩

#assert_trust kernel exists_normalized_minimal_chart
#assert_trust kernel exists_chart_two_symmetricWidths
#print axioms exists_chart_two_symmetricWidths

end NLA.Proofs.TR14
