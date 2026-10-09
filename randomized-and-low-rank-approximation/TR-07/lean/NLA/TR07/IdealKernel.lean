import NLA.TR07.SignedVectors
import NLA.TR07.FinitePaths

/-! A finite signed-column transition with an absorbing zero state. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace NLA.TR07
open Law Matrix

abbrev SignedState (α : Type*) := Option (Bool × α)

def stateVector {α : Type*} {k : ℕ} (u : α → Vec k) : SignedState α → Vec k
  | none => 0
  | some (b,a) => (if b then (-1:ℝ) else 1) • u a

@[simp] theorem stateVector_none {α : Type*} {k : ℕ} (u : α → Vec k) :
    stateVector u none = 0 := rfl

@[simp] theorem stateVector_pos {α : Type*} {k : ℕ} (u : α → Vec k) (a : α) :
    stateVector u (some (false,a)) = u a := by simp [stateVector]

@[simp] theorem stateVector_neg {α : Type*} {k : ℕ} (u : α → Vec k) (a : α) :
    stateVector u (some (true,a)) = -u a := by simp [stateVector]

theorem SignedVector.neg {k s : ℕ} {v : Vec k} (hv : SignedVector s v) :
    SignedVector s (-v) := by
  constructor
  · intro i
    rcases hv.1 i with h | h | h <;> simp [h]
  · simpa using hv.2

theorem stateVector_signed {α : Type*} {k s : ℕ} (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (b : Bool) (a : α) :
    SignedVector s (stateVector u (some (b,a))) := by
  cases b
  · simpa using hu a
  · simpa using (hu a).neg

theorem stateVector_norm_sq_le {α : Type*} {k s : ℕ} (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (x : SignedState α) :
    ‖stateVector u x‖^2 ≤ s := by
  rcases x with _ | ⟨b,a⟩
  · simp
  · exact le_of_eq (stateVector_signed u hu b a).norm_sq

variable {α : Type*} [Fintype α] {k s : ℕ}

/-- Support sampling represented on all coordinates; zero coordinates receive zero mass. -/
def coordinateChoice (v : Vec k) (hv : SignedVector s v) (hs : 0 < s) : Law (Fin k) where
  wt i := v i^2 / s
  nonneg i := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  sum_eq_one := by
    rw [← Finset.sum_div, ← EuclideanSpace.real_norm_sq_eq, hv.norm_sq]
    have : (s:ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    exact div_self this

@[simp] theorem coordinateChoice_wt (v : Vec k) (hv : SignedVector s v) (hs : 0 < s) (i : Fin k) :
    (coordinateChoice v hv hs).wt i = v i^2 / s := rfl

/-- Regularized conditional draw, with its missing mass assigned to the absorbing state. -/
def coordinateDraw (p : Law α) (u : α → Vec k) (hk : 0 < k) (i : Fin k) : Law (Option α) where
  wt x := match x with
    | none => 1 - incidence p u i / regDiagonal p u i
    | some a => p.wt a * (u a i)^2 / regDiagonal p u i
  nonneg x := by
    cases x with
    | none =>
      apply sub_nonneg.mpr
      apply (div_le_one (regDiagonal_pos p u hk i)).mpr
      exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
    | some a =>
      exact div_nonneg (mul_nonneg (p.nonneg a) (sq_nonneg _))
        (regDiagonal_pos p u hk i).le
  sum_eq_one := by
    rw [Fintype.sum_option]
    change (1 - incidence p u i / regDiagonal p u i) +
      (∑ a, p.wt a * (u a i)^2 / regDiagonal p u i) = 1
    rw [← Finset.sum_div]
    change (1 - incidence p u i / regDiagonal p u i) +
      incidence p u i / regDiagonal p u i = 1
    ring

@[simp] theorem coordinateDraw_none (p : Law α) (u : α → Vec k) (hk : 0 < k) (i : Fin k) :
    (coordinateDraw p u hk i).wt none = 1 - incidence p u i / regDiagonal p u i := rfl

@[simp] theorem coordinateDraw_some (p : Law α) (u : α → Vec k) (hk : 0 < k)
    (i : Fin k) (a : α) :
    (coordinateDraw p u hk i).wt (some a) = p.wt a * (u a i)^2 / regDiagonal p u i := rfl

/-- Deterministic sign update shared by ideal and reservoir transitions. -/
def orientDraw (u : α → Vec k) (i : Fin k) (t : ℝ) : Option α → SignedState α :=
  Option.map (fun a => (decide (t * u a i < 0), a))

def coordinateBranch (p : Law α) (u : α → Vec k) (hk : 0 < k) (i : Fin k) (t : ℝ) :
    Law (SignedState α) := (coordinateDraw p u hk i).map (orientDraw u i t)

/-- The ideal signed-column transition. -/
def idealKernel (p : Law α) (u : α → Vec k) (hu : ∀ a, SignedVector s (u a))
    (hk : 0 < k) (hs : 0 < s) : SignedState α → Law (SignedState α)
  | none => Law.pure none
  | some (b,a) =>
    (coordinateChoice (stateVector u (some (b,a))) (stateVector_signed u hu b a) hs).bind
      (fun i => coordinateBranch p u hk i (stateVector u (some (b,a)) i))

omit [Fintype α] in
/-- Orientation multiplies a signed column by the product of the two selected entries. -/
theorem orientDraw_identity (u : α → Vec k) (hu : ∀ a, SignedVector s (u a))
    (v : Vec k) (hv : SignedVector s v) (i : Fin k) (a : α) :
    ((v i)^2 * (u a i)^2) • stateVector u (orientDraw u i (v i) (some a)) =
      (v i * u a i) • u a := by
  rcases hv.1 i with hi | hi | hi <;>
    rcases (hu a).1 i with ha | ha | ha <;>
    norm_num [orientDraw, stateVector, hi, ha]

/-- The coordinate mean, multiplied by the support indicator, in entrywise form. -/
theorem coordinateBranch_mean_entry (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (hk : 0 < k)
    (v : Vec k) (hv : SignedVector s v) (i j : Fin k) :
    (v i)^2 * ((coordinateBranch p u hk i (v i)).mean (stateVector u)) j =
      v i * (covariance p u j i) / regDiagonal p u i := by
  rw [coordinateBranch, mean_map, mean_apply]
  unfold expect
  rw [Fintype.sum_option]
  simp only [orientDraw, Option.map_none, stateVector_none, PiLp.zero_apply, mul_zero, zero_add]
  rw [Finset.mul_sum]
  rw [covariance_apply]
  unfold expect
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have h := congrArg (fun z : Vec k => z j) (orientDraw_identity u hu v hv i a)
  simp only [PiLp.smul_apply, smul_eq_mul] at h
  dsimp [coordinateDraw]
  calc
    _ = p.wt a / regDiagonal p u i *
        ((v i)^2 * (u a i)^2 * stateVector u (orientDraw u i (v i) (some a)) j) := by
      dsimp [orientDraw]
      ring
    _ = _ := by rw [h]; ring

/-- Mean of the ideal transition, before introducing matrix action notation. -/
theorem idealKernel_mean_entry (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (hk : 0 < k) (hs : 0 < s)
    (x : SignedState α) (j : Fin k) :
    ((idealKernel p u hu hk hs x).mean (stateVector u)) j =
      (s:ℝ)⁻¹ * ∑ i, covariance p u j i * (regDiagonal p u i)⁻¹ * stateVector u x i := by
  rcases x with _ | ⟨b,a⟩
  · simp [idealKernel, mean, Law.pure]
  · rw [idealKernel, mean_bind, mean_apply]
    unfold expect
    simp only [coordinateChoice_wt]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := coordinateBranch_mean_entry p u hu hk
      (stateVector u (some (b,a))) (stateVector_signed u hu b a) i j
    calc
      _ = (s:ℝ)⁻¹ * ((stateVector u (some (b,a)) i)^2 *
          ((coordinateBranch p u hk i (stateVector u (some (b,a)) i)).mean (stateVector u)) j) := by ring
      _ = _ := by rw [h]; ring

end NLA.TR07
