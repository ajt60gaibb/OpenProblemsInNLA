import NLA.Proofs.TR04.TTStrictFamily

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04.TensorFormat.TTStrict
namespace Original
open NLA.Computation.TensorTrainApproximation

def formatCast {ns ms : List ℕ} (h : ns = ms) :
    TensorFormat.Tensor ns ≃ₗ[ℝ] TensorFormat.Tensor ms := by
  subst ms
  exact LinearEquiv.refl ℝ _

theorem formatCast_error {ns ms : List ℕ} (h : ns = ms)
    (A X : TensorFormat.Tensor ns) :
    error ns A X = error ms (formatCast h A) (formatCast h X) := by subst ms; rfl

theorem formatCast_feasible {ns ms : List ℕ} (h : ns = ms) (r : ℕ → ℕ)
    (A : TensorFormat.Tensor ns) :
    RankFeasible ns r A ↔ RankFeasible ms r (formatCast h A) := by subst ms; rfl

def input {S : Shape} {ms : List ℕ} (h : modeList S.mode = ms) (A : NLA.Computation.TensorTrainApproximation.Tensor S) :
    TensorFormat.Tensor ms := formatCast h (originalTensorLinearEquiv S A)

def output {S : Shape} {ms : List ℕ} (h : modeList S.mode = ms) (X : TensorFormat.Tensor ms) :
    NLA.Computation.TensorTrainApproximation.Tensor S := (originalTensorLinearEquiv S).symm ((formatCast h).symm X)

@[simp] theorem input_output {S : Shape} {ms : List ℕ} (h : modeList S.mode = ms)
    (X : TensorFormat.Tensor ms) : input h (output h X) = X := by
  simp [input, output]

@[simp] theorem output_input {S : Shape} {ms : List ℕ} (h : modeList S.mode = ms)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S) : output h (input h A) = A := by
  simp [input, output]

theorem input_error {S : Shape} {ms : List ℕ} (h : modeList S.mode = ms) (A X : NLA.Computation.TensorTrainApproximation.Tensor S) :
    FrobeniusSq S A X = error ms (input h A) (input h X) := by
  rw [original_error_eq]
  exact formatCast_error h _ _

theorem output_error {S : Shape} {ms : List ℕ} (h : modeList S.mode = ms)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S) (X : TensorFormat.Tensor ms) :
    FrobeniusSq S A (output h X) = error ms (input h A) X := by
  simpa only [input_output] using input_error h A (output h X)

theorem input_feasible {S : Shape} {ms : List ℕ} (h : modeList S.mode = ms)
    (r : Ranks S) (A : NLA.Computation.TensorTrainApproximation.Tensor S) :
    Feasible S r A ↔ RankFeasible ms (originalRanks S r) (input h A) := by
  rw [original_feasible_iff]
  exact formatCast_feasible h _ _

theorem output_feasible {S : Shape} {ms : List ℕ} (h : modeList S.mode = ms)
    (r : Ranks S) (X : TensorFormat.Tensor ms)
    (hX : RankFeasible ms (originalRanks S r) X) : Feasible S r (output h X) := by
  apply (input_feasible h r _).mpr
  simpa only [input_output] using hX

theorem first_rank_pos (S : Shape) (r : Ranks S) (hr : ∀ j, 1 ≤ r j) :
    1 ≤ originalRanks S r 0 := by
  have h0 : 0 < S.order - 1 := by have := S.order_ge; omega
  simpa only [originalRanks, dif_pos h0] using hr ⟨0, h0⟩

theorem exists_format (S : Shape) :
    ∃ m n : ℕ, ∃ ns : List ℕ, modeList S.mode = m :: n :: ns ∧ 1 ≤ ns.length := by
  have hh : 3 ≤ (modeList S.mode).length := by rw [length_modeList]; exact S.order_ge
  generalize he : modeList S.mode = ms at hh
  cases ms with
  | nil => simp at hh
  | cons m rest =>
    cases rest with
    | nil => simp at hh
    | cons n ns =>
      refine ⟨m, n, ns, rfl, ?_⟩
      simp only [List.length_cons] at hh
      omega

theorem length_pos {S : Shape} {m n : ℕ} {ns : List ℕ}
    (h : modeList S.mode = m :: n :: ns) : 1 ≤ ns.length := by
  have hl := congrArg List.length h
  rw [length_modeList] at hl
  simp only [List.length_cons] at hl
  have := S.order_ge
  omega

theorem length_factor {S : Shape} {m n : ℕ} {ns : List ℕ}
    (h : modeList S.mode = m :: n :: ns) : ((ns.length : ℝ) + 1) = (S.order : ℝ) - 1 := by
  have hl := congrArg List.length h
  rw [length_modeList] at hl
  simp only [List.length_cons] at hl
  have hr : (S.order : ℝ) = (ns.length : ℝ) + 1 + 1 := by exact_mod_cast hl
  linarith

#assert_trust kernel input_error
#assert_trust kernel output_feasible
#assert_trust kernel exists_format
#print axioms output_feasible
end Original
end NLA.Proofs.TR04.TensorFormat.TTStrict
