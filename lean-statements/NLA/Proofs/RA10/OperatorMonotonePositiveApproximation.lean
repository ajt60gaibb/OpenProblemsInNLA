import NLA.Proofs.RA10.OperatorMonotoneClosure

/-! Identify the compact closure with the continuous, strictly positive,
normalized operator-monotone functions on the open half-line. Positive shifts
give admissible functions on the closed half-line and converge pointwise.
This removes an extension-at-zero obligation from the future extremal argument. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.RA10 Set Filter

namespace NLA.Proofs.RA10

theorem orderedPSDSpectralDecomposition_add_const {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ} (hA : OrderedPSDSpectralDecomposition A a Q)
    {c : ℝ} (hc : 0 ≤ c) :
    OrderedPSDSpectralDecomposition (A + c • 1) (fun i => a i + c) Q := by
  refine ⟨fun i => add_nonneg (hA.1 i) hc,
    fun i j hij => add_le_add (hA.2.1 hij) le_rfl, hA.2.2.1, ?_⟩
  have heq := functionMatrix_add (fun x => x) (fun _ => c) a Q
  rw [functionMatrix_const c a Q hA.2.2.1] at heq
  change SpectralMatrix (fun i => a i + c) Q = SpectralMatrix a Q + c • 1 at heq
  rw [hA.2.2.2]
  exact heq.symm

theorem operatorMonotoneOnPositive_shift {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive f) {c : ℝ} (hc : 0 < c) :
    OperatorMonotoneOnNonnegative (fun x => f (x + c)) := by
  intro d hd H G a b QH QG hH hG hHG
  have hdiff : (H + c • 1) - (G + c • 1) = H - G := by abel
  exact hf d hd (H + c • 1) (G + c • 1) (fun i => a i + c) (fun i => b i + c) QH QG
    (fun i => add_pos_of_nonneg_of_pos (hH.1 i) hc)
    (fun i => add_pos_of_nonneg_of_pos (hG.1 i) hc)
    (orderedPSDSpectralDecomposition_add_const hH hc.le)
    (orderedPSDSpectralDecomposition_add_const hG hc.le) (hdiff ▸ hHG)

theorem admissibleFunction_positive_shift {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hpos : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hmono : OperatorMonotoneOnPositive f) {c : ℝ} (hc : 0 < c) :
    AdmissibleFunction (fun x => f (x + c)) := by
  refine ⟨hcont.comp (continuousOn_id.add continuousOn_const) ?_, ?_,
    operatorMonotoneOnPositive_shift hmono hc⟩
  · intro x hx
    exact add_pos_of_nonneg_of_pos hx hc
  · intro x hx
    exact hpos _ (add_pos_of_nonneg_of_pos hx hc)

/-- Normalized shifts of any continuous positive operator-monotone function
converge to it, placing its positive profile in the compact class. -/
theorem positiveOperatorMonotone_mem_compactClass {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hmono : OperatorMonotoneOnPositive f) (h1 : f 1 = 1) :
    (fun x : PositiveArgument => f x) ∈ normalizedAdmissibleCompactClass := by
  let s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hspos (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hs : Tendsto s atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let g : ℕ → ℝ → ℝ := fun n x => (f (1 + s n))⁻¹ * f (x + s n)
  have hg (n : ℕ) : AdmissibleFunction (g n) ∧ g n 1 = 1 :=
    admissibleFunction_normalize
      (admissibleFunction_positive_shift hcont (fun x hx => (hpos x hx).le) hmono (hspos n))
      (hpos _ (add_pos zero_lt_one (hspos n)))
  have hlim (x : ℝ) (hx : 0 < x) :
      Tendsto (fun n => f (x + s n)) atTop (nhds (f x)) := by
    apply (hcont.continuousAt (isOpen_Ioi.mem_nhds hx)).tendsto.comp
    simpa only [add_zero] using (tendsto_const_nhds.add hs :
      Tendsto (fun n => x + s n) atTop (nhds (x + 0)))
  have hlimnorm : Tendsto (fun n => fun x : PositiveArgument => g n x) atTop
      (nhds (fun x : PositiveArgument => f x)) := by
    apply tendsto_pi_nhds.mpr
    intro x
    have hn := ((hlim 1 zero_lt_one).inv₀ (by rw [h1]; norm_num)).mul (hlim x x.property)
    simpa only [g, h1, inv_one, one_mul] using hn
  exact isClosed_closure.mem_of_tendsto hlimnorm (Eventually.of_forall fun n =>
    subset_closure ⟨g n, (hg n).1, (hg n).2, rfl⟩)

/-- An intrinsic description of the class to which Krein–Milman applies.
The derivative and divided-difference facts needed to classify its extreme
points have not been assumed here. -/
theorem mem_normalizedAdmissibleCompactClass_iff {g : PositiveArgument → ℝ} :
    g ∈ normalizedAdmissibleCompactClass ↔
      ContinuousOn (positiveProfileExtension g) (Set.Ioi 0) ∧
      (∀ x, 0 < g x) ∧ g ⟨1, by norm_num [PositiveArgument]⟩ = 1 ∧
      OperatorMonotoneOnPositive (positiveProfileExtension g) := by
  constructor
  · intro hg
    exact ⟨normalizedAdmissibleCompactClass_continuousOn hg,
      normalizedAdmissibleCompactClass_pos hg, normalizedAdmissibleCompactClass_at_one hg,
      normalizedAdmissibleCompactClass_operatorMonotone hg⟩
  · rintro ⟨hcont, hpos, h1, hmono⟩
    have hpos' : ∀ x : ℝ, 0 < x → 0 < positiveProfileExtension g x := by
      intro x hx
      simpa only [positiveProfileExtension, dif_pos hx] using hpos ⟨x, hx⟩
    have h1' : positiveProfileExtension g 1 = 1 := by
      simpa only [positiveProfileExtension, dif_pos zero_lt_one] using h1
    have hmem := positiveOperatorMonotone_mem_compactClass hcont hpos' hmono h1'
    simpa only [positiveProfileExtension_apply] using hmem

#assert_trust kernel orderedPSDSpectralDecomposition_add_const
#assert_trust kernel operatorMonotoneOnPositive_shift
#assert_trust kernel admissibleFunction_positive_shift
#assert_trust kernel positiveOperatorMonotone_mem_compactClass
#assert_trust kernel mem_normalizedAdmissibleCompactClass_iff
#print axioms mem_normalizedAdmissibleCompactClass_iff

end NLA.Proofs.RA10
