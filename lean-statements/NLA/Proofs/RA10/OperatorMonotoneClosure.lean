import NLA.Proofs.RA10.OperatorMonotoneCompactness
import Mathlib.Analysis.Convex.FunctionTopology
import Mathlib.Analysis.Convex.Continuous

/-! Properties of the compact closure on the strictly positive half-line.
These lemmas justify using the compact class in an extreme-point argument:
normalization, strict positivity, concavity, continuity and all-size matrix
monotonicity survive. No continuity at zero is claimed for closure members. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.RA10 Set

namespace NLA.Proofs.RA10

/-- An arbitrary extension used only to apply the usual real-function APIs.
Its value at nonpositive arguments is irrelevant to the positive-domain results. -/
noncomputable def positiveProfileExtension (g : PositiveArgument → ℝ) (x : ℝ) : ℝ :=
  if hx : 0 < x then g ⟨x, hx⟩ else 0

theorem positiveProfileExtension_apply (g : PositiveArgument → ℝ) (x : PositiveArgument) :
    positiveProfileExtension g x = g x := by
  simp only [positiveProfileExtension, dif_pos (show 0 < (x : ℝ) from x.property)]

theorem positiveProfileExtension_continuous : Continuous positiveProfileExtension := by
  apply continuous_pi
  intro x
  by_cases hx : 0 < x
  · simpa only [positiveProfileExtension, dif_pos hx] using
      (continuous_apply (⟨x, hx⟩ : PositiveArgument))
  · simpa only [positiveProfileExtension, dif_neg hx] using
      (continuous_const : Continuous (fun _ : PositiveArgument → ℝ => (0 : ℝ)))

theorem normalizedAdmissibleCompactClass_bounds {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) (x : PositiveArgument) :
    min 1 (x : ℝ) ≤ g x ∧ g x ≤ max 1 (x : ℝ) := by
  have hc : IsClosed {g : PositiveArgument → ℝ |
      min 1 (x : ℝ) ≤ g x ∧ g x ≤ max 1 (x : ℝ)} :=
    (isClosed_le continuous_const (continuous_apply x)).inter
      (isClosed_le (continuous_apply x) continuous_const)
  apply closure_minimal (t := {g | min 1 (x : ℝ) ≤ g x ∧ g x ≤ max 1 (x : ℝ)}) ?_ hc hg
  rintro _ ⟨f, hf, h1, rfl⟩
  simpa [h1] using admissibleFunction_bounds hf x.property.le

theorem normalizedAdmissibleCompactClass_at_one {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) :
    g ⟨1, by norm_num [PositiveArgument]⟩ = 1 := by
  have hb := normalizedAdmissibleCompactClass_bounds hg ⟨1, by norm_num [PositiveArgument]⟩
  simp only [min_self, max_self] at hb
  exact le_antisymm hb.2 hb.1

theorem normalizedAdmissibleCompactClass_pos {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) (x : PositiveArgument) : 0 < g x :=
  (lt_min zero_lt_one x.property).trans_le (normalizedAdmissibleCompactClass_bounds hg x).1

theorem normalizedAdmissibleCompactClass_concaveOn {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) :
    ConcaveOn ℝ (Set.Ioi 0) (positiveProfileExtension g) := by
  have hc : IsClosed {g : PositiveArgument → ℝ |
      ConcaveOn ℝ (Set.Ioi 0) (positiveProfileExtension g)} :=
    isClosed_setOfPred_concaveOn.preimage positiveProfileExtension_continuous
  apply closure_minimal (t := {g | ConcaveOn ℝ (Set.Ioi 0) (positiveProfileExtension g)}) ?_ hc hg
  rintro _ ⟨f, hf, h1, rfl⟩
  apply ((admissibleFunction_concaveOn hf).subset Ioi_subset_Ici_self (convex_Ioi 0)).congr
  intro x hx
  change 0 < x at hx
  simp [positiveProfileExtension, hx]

theorem normalizedAdmissibleCompactClass_continuousOn {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) :
    ContinuousOn (positiveProfileExtension g) (Set.Ioi 0) :=
  (normalizedAdmissibleCompactClass_concaveOn hg).continuousOn isOpen_Ioi

theorem isClosed_setOf_positiveSemidefinite {n : ℕ} :
    IsClosed {M : Matrix (Fin n) (Fin n) ℝ | PositiveSemidefinite M} := by
  simp only [PositiveSemidefinite, Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (by fun_prop) (by fun_prop)
  · exact isClosed_iInter fun x => isClosed_le (by fun_prop) (by fun_prop)

theorem functionMatrix_map_continuous {n : ℕ} (a : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun f : ℝ → ℝ => FunctionMatrix f a Q) := by
  unfold FunctionMatrix SpectralMatrix
  fun_prop

/-- The same real spectral-sum order as the frozen definition, restricted to
strictly positive spectra. It makes no assertion about the extension at zero. -/
def OperatorMonotoneOnPositive (f : ℝ → ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → ∀ H G : Matrix (Fin d) (Fin d) ℝ,
    ∀ a b : Fin d → ℝ, ∀ QH QG : Matrix (Fin d) (Fin d) ℝ,
      (∀ i, 0 < a i) → (∀ i, 0 < b i) →
      OrderedPSDSpectralDecomposition H a QH →
      OrderedPSDSpectralDecomposition G b QG →
      PositiveSemidefinite (H - G) →
      PositiveSemidefinite (FunctionMatrix f a QH - FunctionMatrix f b QG)

theorem isClosed_setOf_operatorMonotoneOnPositive :
    IsClosed {f : ℝ → ℝ | OperatorMonotoneOnPositive f} := by
  simp only [OperatorMonotoneOnPositive, Set.ofPred_forall]
  refine isClosed_iInter fun d => isClosed_iInter fun hd =>
    isClosed_iInter fun H => isClosed_iInter fun G =>
    isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun QH => isClosed_iInter fun QG =>
    isClosed_iInter fun ha => isClosed_iInter fun hb =>
    isClosed_iInter fun hH => isClosed_iInter fun hG =>
    isClosed_iInter fun hHG => ?_
  exact isClosed_setOf_positiveSemidefinite.preimage
    ((functionMatrix_map_continuous a QH).sub (functionMatrix_map_continuous b QG))

theorem normalizedAdmissibleCompactClass_operatorMonotone {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) :
    OperatorMonotoneOnPositive (positiveProfileExtension g) := by
  have hc : IsClosed {g : PositiveArgument → ℝ |
      OperatorMonotoneOnPositive (positiveProfileExtension g)} :=
    isClosed_setOf_operatorMonotoneOnPositive.preimage positiveProfileExtension_continuous
  apply closure_minimal
    (t := {g | OperatorMonotoneOnPositive (positiveProfileExtension g)}) ?_ hc hg
  rintro _ ⟨f, hf, h1, rfl⟩
  intro d hd H G a b QH QG ha hb hH hG hHG
  have heqa : FunctionMatrix (positiveProfileExtension (fun x : PositiveArgument => f x)) a QH =
      FunctionMatrix f a QH := functionMatrix_congr a QH fun i => by
    simp [positiveProfileExtension, ha i]
  have heqb : FunctionMatrix (positiveProfileExtension (fun x : PositiveArgument => f x)) b QG =
      FunctionMatrix f b QG := functionMatrix_congr b QG fun i => by
    simp [positiveProfileExtension, hb i]
  rw [heqa, heqb]
  exact hf.2.2 d hd H G a b QH QG hH hG hHG

#assert_trust kernel positiveProfileExtension_apply
#assert_trust kernel positiveProfileExtension_continuous
#assert_trust kernel normalizedAdmissibleCompactClass_bounds
#assert_trust kernel normalizedAdmissibleCompactClass_at_one
#assert_trust kernel normalizedAdmissibleCompactClass_pos
#assert_trust kernel normalizedAdmissibleCompactClass_concaveOn
#assert_trust kernel normalizedAdmissibleCompactClass_continuousOn
#assert_trust kernel isClosed_setOf_positiveSemidefinite
#assert_trust kernel functionMatrix_map_continuous
#assert_trust kernel isClosed_setOf_operatorMonotoneOnPositive
#assert_trust kernel normalizedAdmissibleCompactClass_operatorMonotone
#print axioms normalizedAdmissibleCompactClass_operatorMonotone

end NLA.Proofs.RA10
