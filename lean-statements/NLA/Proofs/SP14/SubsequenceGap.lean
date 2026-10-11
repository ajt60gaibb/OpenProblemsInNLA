import NLA.Statements.SP14

/-!
SP-14: a conditional bridge from a separated subsequence to the negative
answer. This does not construct the source symbol or establish its finite
Toeplitz multiplicity estimates.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Filter

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

/-- A positive eventual real-part gap along strictly increasing actual
Toeplitz orders contradicts the original full-sequence complex limit. -/
theorem target_of_subsequence_gap
    (a : Circle → ℂ) (F : ℂ → ℂ) (n : ℕ → ℕ) (δ : ℝ)
    (ha : Continuous a)
    (hinner : ¬ InnerExtension a) (houter : ¬ OuterExtension a)
    (hFcont : Continuous F) (hFcompact : HasCompactSupport F)
    (hcanon : Canonical a F = 0)
    (hn : StrictMono n) (hδ : 0 < δ)
    (hgap : ∀ᶠ j in atTop, δ ≤ (Empirical a F (n j)).re) : Target := by
  intro horiginal
  have hfull : Tendsto (fun k : ℕ => Empirical a F k) atTop (nhds (0 : ℂ)) := by
    simpa [hcanon] using horiginal a ha hinner houter F hFcont hFcompact
  have hsub : Tendsto (fun j : ℕ => Empirical a F (n j)) atTop (nhds (0 : ℂ)) :=
    hfull.comp hn.tendsto_atTop
  have hre : Tendsto (fun j : ℕ => (Empirical a F (n j)).re)
      atTop (nhds (0 : ℝ)) := by
    simpa [Function.comp_def] using (Complex.continuous_re.tendsto (0 : ℂ)).comp hsub
  have hsmall : ∀ᶠ j in atTop, (Empirical a F (n j)).re < δ :=
    hre.eventually_lt_const hδ
  obtain ⟨j, hjgap, hjsmall⟩ := (hgap.and hsmall).exists
  exact (not_lt_of_ge hjgap) hjsmall

#assert_trust kernel target_of_subsequence_gap
#print axioms target_of_subsequence_gap

end NLA.Proofs.SP14
