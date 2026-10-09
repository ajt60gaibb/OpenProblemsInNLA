import NLA.Computation.BandIntervals
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! Small kernel-checked controls for the compact grammar and the singular
scope which the historical hull scaffold did not represent correctly.
These examples neither provide a polynomial algorithm nor prove a Target. -/
set_option autoImplicit false

namespace NLA.Computation.BandIntervalControls

open BandIntervals BinaryEncoding

private abbrev stampedBand : BandInput where
  n := 3
  diagonal := ![⟨1, 2⟩, ⟨3, 4⟩, ⟨5, 6⟩]
  upper := ![⟨7, 8⟩, ⟨9, 10⟩]
  lower := ![⟨11, 12⟩, ⟨13, 14⟩]

/-- All fourteen endpoints occur once in diagonal/upper/lower order. -/
example : encodeBand stampedBand = encodeNat 3 ++
    encodeRats [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] := by
  simp [encodeBand, stampedBand, BandIntervals.encodeInterval, encodeRats, List.ofFn_succ, List.append_assoc]

private abbrev stampedSystem : SystemInput where
  band := stampedBand
  rhs := ![⟨15, 16⟩, ⟨17, 18⟩, ⟨19, 20⟩]

/-- RHS endpoint pairs follow the bands with no second dimension header. -/
example : encodeSystem stampedSystem = encodeNat 3 ++
    encodeRats [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
      15, 16, 17, 18, 19, 20] := by
  simp [encodeSystem, stampedSystem, encodeBand, stampedBand, BandIntervals.encodeInterval,
    encodeRats, List.ofFn_succ, List.append_assoc]

example : encodeHull (HullOutput.empty : HullOutput 2) = [false] := by rfl

/-- Both infinity meanings and exact finite rational tags coexist in one box. -/
example : encodeHull (HullOutput.box
    ![LowerEndpoint.negativeInfinity, LowerEndpoint.finite (-3 / 2)]
    ![UpperEndpoint.finite (7 / 3), UpperEndpoint.positiveInfinity]) =
    [true] ++ encodeNat 2 ++ [false, true] ++ encodeRat (7 / 3) ++
      [true] ++ encodeRat (-3 / 2) ++ [false] := by
  simp [encodeHull, encodeLower, encodeUpper, List.ofFn_succ, List.append_assoc]

example : encodeHull (HullOutput.empty : HullOutput 1) ≠
    encodeHull (HullOutput.box (fun _ => .finite 0) (fun _ => .finite 0) : HullOutput 1) := by
  decide

private abbrev zeroBand : BandInput where
  n := 1
  diagonal := fun _ => ⟨0, 0⟩
  upper := Fin.elim0
  lower := Fin.elim0

private abbrev zeroSystem : SystemInput where
  band := zeroBand
  rhs := fun _ => ⟨0, 0⟩

private theorem zeroSolution (x : Fin 1 → ℝ) : x ∈ SolutionSet zeroSystem := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      norm_num [zeroSystem, zeroBand, RationalInterval.Contains]
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · intros
      rfl
  · intro i
    norm_num [zeroSystem, RationalInterval.Contains]
  · simp

/-- A singular consistent one-dimensional system has the full real hull. -/
example : CorrectHull zeroSystem
    (.box (fun _ => .negativeInfinity) (fun _ => .positiveInfinity)) := by
  refine ⟨⟨0, zeroSolution 0⟩, ?_⟩
  intro i
  constructor
  · intro R
    exact ⟨fun _ => R - 1, zeroSolution _, sub_lt_self R zero_lt_one⟩
  · intro R
    exact ⟨fun _ => R + 1, zeroSolution _, lt_add_of_pos_right R zero_lt_one⟩

private abbrev inconsistentSystem : SystemInput where
  band := zeroBand
  rhs := fun _ => ⟨1, 1⟩

/-- A singular inconsistent system uses the one global empty output. -/
example : CorrectHull inconsistentSystem .empty := by
  change SolutionSet inconsistentSystem = ∅
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases hx with ⟨T, b, hT, hb, hEq⟩
  have td := hT.1 0
  have bd := hb 0
  have he := congrFun hEq 0
  have t0 : T 0 0 = 0 := by
    have h : (0 : ℝ) ≤ T 0 0 ∧ T 0 0 ≤ 0 := by
      simpa [RationalInterval.Contains] using td
    exact le_antisymm h.2 h.1
  have b0 : b 0 = 1 := by
    have h : (1 : ℝ) ≤ b 0 ∧ b 0 ≤ 1 := by
      simpa [RationalInterval.Contains] using bd
    exact le_antisymm h.2 h.1
  simp [Matrix.mulVec, dotProduct, t0, b0] at he

/-- Disconnected coordinate projections still have their true infinite bounds.
This is the shape of the n=1 [-1,1] x = 1 counterexample to the old scaffold. -/
private abbrev separated : Set (Fin 1 → ℝ) := {x | x 0 ≤ -1 ∨ 1 ≤ x 0}

example : LowerCorrect separated (0 : Fin 1) .negativeInfinity ∧
    UpperCorrect separated (0 : Fin 1) .positiveInfinity := by
  constructor
  · intro R
    refine ⟨fun _ => min (R - 1) (-1), Or.inl (min_le_right _ _), ?_⟩
    exact lt_of_le_of_lt (min_le_left _ _) (sub_lt_self R zero_lt_one)
  · intro R
    refine ⟨fun _ => max (R + 1) 1, Or.inr (le_max_right _ _), ?_⟩
    exact lt_of_lt_of_le (lt_add_of_pos_right R zero_lt_one) (le_max_left _ _)

example : (fun _ : Fin 1 => (0 : ℝ)) ∉ separated := by norm_num

end NLA.Computation.BandIntervalControls
