import NLA.IE03.Certificate.Checkpoint
import NLA.IE03.Walsh
import Mathlib.Data.Rat.Cast.Order

/-! Exact integer comparisons and identities certify Schur updates over ℝ. -/

namespace NLA.IE03.Certificate

open NLA.IE03

def square (n : ℕ) (test : ℕ → ℕ → Bool) : Bool :=
  (List.range n).all fun i => (List.range n).all (test i)

theorem square_sound {n : ℕ} {test : ℕ → ℕ → Bool} (h : square n test = true)
    {i j : ℕ} (hi : i < n) (hj : j < n) : test i j = true := by
  simp only [square, List.all_eq_true, List.mem_range] at h
  exact h i hi j hj

noncomputable def Checkpoint.entries (A : Checkpoint) : Entries ℝ :=
  fun i j => (A.numerator i j : ℝ) / (A.denominator : ℝ)

def Checkpoint.pivotMagnitude (A : Checkpoint) (r c : ℕ) : ℚ :=
  ((A.numerator r c).natAbs : ℚ) / (A.denominator : ℚ)

private theorem abs_cast (v : ℤ) : |(v : ℝ)| = (v.natAbs : ℝ) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

private theorem Checkpoint.abs_entries (A : Checkpoint) (i j : ℕ) :
    |A.entries i j| = (A.pivotMagnitude i j : ℝ) := by
  simp only [Checkpoint.entries, Checkpoint.pivotMagnitude, abs_div, abs_cast,
    Rat.cast_div, Rat.cast_natCast,
    abs_of_nonneg (Nat.cast_nonneg A.denominator : (0 : ℝ) ≤ A.denominator)]

/-- For an active matrix of order `n + 1`, check the selected pivot and
all `n²` entries of the next checkpoint after clearing denominators. -/
def stepOK (n : ℕ) (A B : Checkpoint) (r c : ℕ) : Bool :=
  let p := A.numerator r c
  decide (r < n + 1 ∧ c < n + 1 ∧ 0 < A.denominator ∧ 0 < B.denominator ∧ p ≠ 0) &&
    (square (n + 1) (fun i j => decide ((A.numerator i j).natAbs ≤ p.natAbs)) &&
     square n (fun i j => decide (
      (A.numerator (skip r i) (skip c j) * p -
        A.numerator (skip r i) c * A.numerator r (skip c j)) * (B.denominator : ℤ) =
      B.numerator i j * ((A.denominator : ℤ) * p))))

theorem step_sound {n r c : ℕ} {A B : Checkpoint} (h : stepOK n A B r c = true) :
    IsPivot (n + 1) A.entries r c ∧ Agree n (schur A.entries r c) B.entries := by
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hr, hc, hA, hB, hp⟩, hbound, hupdate⟩ := h
  have hdA : (0 : ℝ) < A.denominator := by exact_mod_cast hA
  have hdB : (0 : ℝ) < B.denominator := by exact_mod_cast hB
  have hpR : (A.numerator r c : ℝ) ≠ 0 := by exact_mod_cast hp
  refine ⟨⟨hr, hc, div_ne_zero hpR hdA.ne', ?_⟩, ?_⟩
  · intro i j hi hj
    have hb := of_decide_eq_true (square_sound hbound hi hj)
    simp only [Checkpoint.entries, abs_div, abs_cast, abs_of_pos hdA]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hb) hdA.le
  · intro i j hi hj
    have he := of_decide_eq_true (square_sound hupdate hi hj)
    have heR := congrArg (fun v : ℤ => (v : ℝ)) he
    push_cast at heR
    let p : ℝ := A.numerator r c
    let x : ℝ := A.numerator (skip r i) (skip c j)
    let y : ℝ := A.numerator (skip r i) c
    let z : ℝ := A.numerator r (skip c j)
    let v : ℝ := B.numerator i j
    let d : ℝ := A.denominator
    let e : ℝ := B.denominator
    change x / d - (y / d) * (z / d) / (p / d) = v / e
    calc
      _ = (x * p - y * z) / (d * p) := by
        field_simp [show d ≠ 0 from hdA.ne', show p ≠ 0 from hpR]
      _ = _ := (div_eq_div_iff (mul_ne_zero hdA.ne' hpR) hdB.ne').2 heR

abbrev Step := ℕ × ℕ × Checkpoint

def endpoint : Checkpoint → List Step → Checkpoint
  | A, [] => A
  | _, (_, _, B) :: rest => endpoint B rest

def peak : Checkpoint → List Step → ℚ
  | _, [] => 0
  | A, (r, c, B) :: rest => max (A.pivotMagnitude r c) (peak B rest)

def traceOK : ℕ → Checkpoint → List Step → Bool
  | _, _, [] => true
  | 0, _, _ :: _ => false
  | n + 1, A, (r, c, B) :: rest => stepOK n A B r c && traceOK n B rest

theorem trace_sound {n : ℕ} {A : Checkpoint} {steps : List Step}
    (h : traceOK n A steps = true) :
    Trace n A.entries (n - steps.length) (endpoint A steps).entries (peak A steps : ℝ) := by
  induction steps generalizing n A with
  | nil =>
    simpa [peak, endpoint] using Trace.empty n A.entries
  | cons step rest ih =>
    obtain ⟨r, c, B⟩ := step
    cases n with
    | zero => simp [traceOK] at h
    | succ n =>
      have hc : stepOK n A B r c = true ∧ traceOK n B rest = true := by
        simpa only [traceOK, Bool.and_eq_true] using h
      obtain ⟨hp, hu⟩ := step_sound hc.1
      have ht := Trace.step hp ((ih hc.2).start hu.symm)
      simpa only [peak, endpoint, List.length_cons, Nat.succ_sub_succ_eq_sub,
        Rat.cast_max, Checkpoint.abs_entries] using ht

/-- Check that the first checkpoint represents the order-16 Sylvester matrix. -/
def seedOK (A : Checkpoint) : Bool :=
  decide (0 < A.denominator) &&
    square 16 (fun i j => decide (A.numerator i j =
      (walsh (K := ℤ) 4 i j) * (A.denominator : ℤ)))

theorem seed_sound {A : Checkpoint} (h : seedOK A = true) :
    Agree 16 (walsh 4) A.entries := by
  simp only [seedOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have hd : (A.denominator : ℝ) ≠ 0 := by exact_mod_cast h.1.ne'
  intro i j hi hj
  have he := of_decide_eq_true (square_sound h.2 hi hj)
  rw [walsh_cast, Checkpoint.entries, eq_div_iff hd]
  exact_mod_cast he.symm

/-- Compare the next stage's first checkpoint with the previous stage's
endpoint tensored with two order-two Sylvester factors. -/
def liftOK (n : ℕ) (A B : Checkpoint) : Bool :=
  decide (0 < A.denominator ∧ 0 < B.denominator) &&
    square (2 * (2 * n)) (fun i j => decide (
      double (double A.numerator) i j * (B.denominator : ℤ) =
        B.numerator i j * (A.denominator : ℤ)))

private theorem double_div (f : Entries ℤ) (d : ℝ) :
    double (fun i j => (f i j : ℝ) / d) =
      fun i j => ((double f i j : ℤ) : ℝ) / d := by
  funext i j
  simp only [double]
  split <;> simp [neg_div]

theorem lift_sound {n : ℕ} {A B : Checkpoint} (h : liftOK n A B = true) :
    Agree (2 * (2 * n)) (double (double A.entries)) B.entries := by
  simp only [liftOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hA, hB⟩, ht⟩ := h
  have hdA : (A.denominator : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hdB : (B.denominator : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  intro i j hi hj
  have he := of_decide_eq_true (square_sound ht hi hj)
  change double (double (fun u v => (A.numerator u v : ℝ) / (A.denominator : ℝ))) i j =
    (B.numerator i j : ℝ) / (B.denominator : ℝ)
  rw [double_div A.numerator, double_div (double A.numerator), div_eq_div_iff hdA hdB]
  exact_mod_cast he

end NLA.IE03.Certificate
