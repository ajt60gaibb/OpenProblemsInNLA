import NLA.Proofs.RE06.GaussianWarmStartResidual

/-! Measurability of the exact first-minimum scan and the actual warm index.
The proofs use its finite comparisons, without a measurable-SVD assumption. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_score_at_finite_index {m : ℕ} (score : Fin (m + 2) → Ω → ℝ)
    (hscore : ∀ b, Measurable (score b)) (K : Ω → Fin (m + 2)) (hK : Measurable K) :
    Measurable (fun ω => score (K ω) ω) := by
  classical
  have he : (fun ω => score (K ω) ω) =
      (fun ω => ∑ b : Fin (m + 2), if K ω = b then score b ω else 0) := by
    funext ω
    simp
  rw [he]
  apply Finset.measurable_sum
  intro b _
  exact Measurable.ite (hK (measurableSet_singleton b)) (hscore b) measurable_const

theorem measurable_scan_minimum {m : ℕ} (score : Fin (m + 2) → Ω → ℝ)
    (hscore : ∀ b, Measurable (score b)) (l : List (Fin (m + 2)))
    (initial : Ω → Fin (m + 2)) (hi : Measurable initial) :
    Measurable (fun ω => l.foldl
      (fun best j => if score j ω < score best ω then j else best) (initial ω)) := by
  induction l generalizing initial with
  | nil => exact hi
  | cons j l ih =>
      have hs := measurable_score_at_finite_index score hscore initial hi
      have hstep : Measurable (fun ω => if score j ω < score (initial ω) ω then j else initial ω) :=
        Measurable.ite (measurableSet_lt (hscore j) hs) measurable_const hi
      simpa only [List.foldl_cons] using ih _ hstep

theorem measurable_minimumIndex {m : ℕ} (score : Fin (m + 2) → Ω → ℝ)
    (hscore : ∀ b, Measurable (score b)) :
    Measurable (fun ω => minimumIndex (fun b => score b ω)) :=
  measurable_scan_minimum score hscore (List.finRange (m + 2)) (fun _ => 0) measurable_const

/-- The same exact score scan, with only the first block as input. -/
def warmIndexFromEntries {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (q : ℕ) (G : Fin n → Fin q → ℝ) : Fin (m + 2) :=
  minimumIndex (fun b => squaredFrobenius (A * Matrix.of G) (F b * Matrix.of G))

theorem warmIndexFromEntries_measurable {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (q : ℕ) :
    Measurable (warmIndexFromEntries F A q) := by
  unfold warmIndexFromEntries
  refine measurable_minimumIndex (fun b G =>
    squaredFrobenius (A * Matrix.of G) (F b * Matrix.of G)) ?_
  intro b
  apply Continuous.measurable
  simp only [squaredFrobenius, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem gaussianWarmIndex_measurable {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (q offset : ℕ) :
    Measurable (gaussianWarmIndex F A q offset) := by
  change Measurable (warmIndexFromEntries F A q ∘
    (fun ω : ℕ → ℝ => fun i j => gaussianBlock n q offset ω i j))
  apply (warmIndexFromEntries_measurable F A q).comp
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact measurable_pi_apply (gaussianBlockIndex n offset (i, j))

/-- No sketch-branch premise is needed to establish actual index measurability. -/
theorem sketchWarmIndex_measurable {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Measurable (fun ω => sketchWarmIndex F A (makePlan n m ε ω)) := by
  by_cases hfull : n ≤ firstWidth m ε + secondWidth m ε + thirdWidth m ε
  · have he : (fun ω => sketchWarmIndex F A (makePlan n m ε ω)) =
        (fun _ : ℕ → ℝ => minimumIndex (fun b : Fin (m + 2) =>
          squaredFrobenius (A * (0 : Matrix (Fin n) (Fin 0) ℝ))
            (F b * (0 : Matrix (Fin n) (Fin 0) ℝ)))) := by
      funext ω
      have hp : makePlan n m ε ω =
          { full := true, s := 0, k := 0, ell := 0, G0 := 0, G1 := 0, H := 0 } := by
        simp only [makePlan, hfull, ↓reduceIte]
      rw [hp]
      rfl
    rw [he]
    exact measurable_const
  · have hsketch : firstWidth m ε + secondWidth m ε + thirdWidth m ε < n := Nat.lt_of_not_ge hfull
    have he : (fun ω => sketchWarmIndex F A (makePlan n m ε ω)) =
        gaussianWarmIndex F A (firstWidth m ε) 0 := by
      funext ω
      exact (gaussianWarmIndex_eq_sketchWarmIndex F A ε hsketch ω).symm
    rw [he]
    exact gaussianWarmIndex_measurable F A (firstWidth m ε) 0

#assert_trust kernel measurable_score_at_finite_index
#assert_trust kernel measurable_scan_minimum
#assert_trust kernel measurable_minimumIndex
#assert_trust kernel warmIndexFromEntries_measurable
#assert_trust kernel gaussianWarmIndex_measurable
#assert_trust kernel sketchWarmIndex_measurable
#print axioms measurable_score_at_finite_index
#print axioms measurable_scan_minimum
#print axioms measurable_minimumIndex
#print axioms warmIndexFromEntries_measurable
#print axioms gaussianWarmIndex_measurable
#print axioms sketchWarmIndex_measurable
end NLA.Proofs.RE06
