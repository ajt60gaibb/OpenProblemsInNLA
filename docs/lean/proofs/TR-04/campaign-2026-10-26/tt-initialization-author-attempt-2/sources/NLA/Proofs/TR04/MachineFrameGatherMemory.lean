import NLA.Proofs.TR04.MachineTraceComposition

/-! Memory specification for actual prefix/cyclic frame materialization.
Remainders occur only in the specification; the program uses an incrementing
counter and explicit wrap comparison. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

structure FrameGatherParameters where
  rows : ℕ
  above : ℕ
  tied : ℕ
  take : ℕ
  start : ℕ
  inputBase : ℕ
  outputBase : ℕ

def FrameGatherParameters.width (P : FrameGatherParameters) : ℕ := P.above + P.take

structure FrameGatherParameters.Valid (P : FrameGatherParameters) : Prop where
  tied_pos : 0 < P.tied
  start_lt : P.start < P.tied
  take_le : P.take ≤ P.tied
  above_le : P.above ≤ P.rows
  cyclic_fits : 0 < P.take → P.above + P.tied ≤ P.rows

def FrameGatherParameters.counter (P : FrameGatherParameters) (k : ℕ) : ℕ :=
  (P.start + (k - P.above)) % P.tied

def FrameGatherParameters.column (P : FrameGatherParameters) (k : ℕ) : ℕ :=
  if k < P.above then k else P.above + P.counter k

def FrameGatherParameters.sourceAddress (P : FrameGatherParameters) (q : ℕ) : ℕ :=
  P.inputBase + (q / P.width) * P.rows + P.column (q % P.width)

theorem FrameGatherParameters.Valid.width_le {P : FrameGatherParameters} (hP : P.Valid) :
    P.width ≤ P.rows := by
  unfold FrameGatherParameters.width
  by_cases hs : P.take = 0
  · simpa only [hs, Nat.add_zero] using hP.above_le
  · exact (Nat.add_le_add_left hP.take_le P.above).trans (hP.cyclic_fits (by omega))

theorem FrameGatherParameters.counter_prefix {P : FrameGatherParameters} (hP : P.Valid)
    (k : ℕ) (hk : k ≤ P.above) : P.counter k = P.start := by
  simp only [counter, Nat.sub_eq_zero_of_le hk, Nat.add_zero, Nat.mod_eq_of_lt hP.start_lt]

theorem FrameGatherParameters.counter_lt {P : FrameGatherParameters} (hP : P.Valid) (k : ℕ) :
    P.counter k < P.tied := Nat.mod_lt _ hP.tied_pos

theorem FrameGatherParameters.counter_succ {P : FrameGatherParameters} (hP : P.Valid)
    (k : ℕ) (hk : P.above ≤ k) :
    P.counter (k + 1) = if P.counter k + 1 = P.tied then 0 else P.counter k + 1 := by
  unfold counter
  rw [show P.start + (k + 1 - P.above) = (P.start + (k - P.above)) + 1 by omega,
    ← Nat.mod_add_mod _ P.tied 1]
  have hc := Nat.mod_lt (P.start + (k - P.above)) hP.tied_pos
  split_ifs with he
  · rw [he, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem FrameGatherParameters.column_lt {P : FrameGatherParameters} (hP : P.Valid)
    (k : ℕ) (hk : k < P.width) : P.column k < P.rows := by
  unfold column
  split_ifs with hh
  · exact hh.trans_le hP.above_le
  · have hs : 0 < P.take := by dsimp [width] at hk; omega
    exact (Nat.add_lt_add_left (P.counter_lt hP k) P.above).trans_le (hP.cyclic_fits hs)

theorem FrameGatherParameters.sourceAddress_flat (P : FrameGatherParameters)
    (i k : ℕ) (hk : k < P.width) :
    P.sourceAddress (i * P.width + k) = P.inputBase + i * P.rows + P.column k := by
  have hw : 0 < P.width := by omega
  have hd : (i * P.width + k) / P.width = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hk, Nat.zero_add]
  have hm : (i * P.width + k) % P.width = k := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hk]
  simp only [sourceAddress, hd, hm]

theorem FrameGatherParameters.sourceAddress_mem {P : FrameGatherParameters} (hP : P.Valid)
    (q : ℕ) (hq : q < P.rows * P.width) :
    P.inputBase ≤ P.sourceAddress q ∧ P.sourceAddress q < P.inputBase + P.rows * P.rows := by
  have hw : 0 < P.width := by
    by_contra hn
    have hz : P.width = 0 := by omega
    rw [hz, Nat.mul_zero] at hq
    omega
  have hi : q / P.width < P.rows := (Nat.div_lt_iff_lt_mul hw).mpr hq
  have hk := P.column_lt hP (q % P.width) (Nat.mod_lt _ hw)
  have hm : (q / P.width + 1) * P.rows ≤ P.rows * P.rows :=
    Nat.mul_le_mul (by omega) le_rfl
  rw [Nat.add_mul, Nat.one_mul] at hm
  dsimp [sourceAddress]
  constructor <;> omega

def frameGatherMemory (memory : ℕ → ℝ) (P : FrameGatherParameters) (count address : ℕ) : ℝ :=
  if P.outputBase ≤ address ∧ address < P.outputBase + count then
    memory (P.sourceAddress (address - P.outputBase)) else memory address

theorem frameGatherMemory_zero (memory : ℕ → ℝ) (P : FrameGatherParameters) :
    frameGatherMemory memory P 0 = memory := by funext a; simp [frameGatherMemory]

theorem frameGatherMemory_outside (memory : ℕ → ℝ) (P : FrameGatherParameters) (n a : ℕ)
    (ha : ¬ (P.outputBase ≤ a ∧ a < P.outputBase + n)) :
    frameGatherMemory memory P n a = memory a := by simp [frameGatherMemory, ha]

theorem frameGatherMemory_succ (memory : ℕ → ℝ) (P : FrameGatherParameters) (n : ℕ) :
    Function.update (frameGatherMemory memory P n) (P.outputBase + n)
      (memory (P.sourceAddress n)) = frameGatherMemory memory P (n + 1) := by
  funext a
  by_cases ha : a = P.outputBase + n
  · subst a
    simp [frameGatherMemory]
  · rw [Function.update_of_ne ha]
    unfold frameGatherMemory
    by_cases hn : P.outputBase ≤ a ∧ a < P.outputBase + n
    · have hn' : P.outputBase ≤ a ∧ a < P.outputBase + (n + 1) := by omega
      rw [if_pos hn, if_pos hn']
    · have hn' : ¬ (P.outputBase ≤ a ∧ a < P.outputBase + (n + 1)) := by omega
      rw [if_neg hn, if_neg hn']

theorem frameGatherMemory_input (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (n : ℕ) (hn : n ≤ P.rows * P.width) (a : ℕ)
    (ha : P.inputBase ≤ a ∧ a < P.inputBase + P.rows * P.rows) :
    frameGatherMemory memory P n a = memory a := by
  apply frameGatherMemory_outside
  rcases hd with hz | hz | hsd | hds <;> omega

theorem frameGatherMemory_read (memory : ℕ → ℝ) (P : FrameGatherParameters) (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (n : ℕ) (hn : n ≤ P.rows * P.width) (q : ℕ) (hq : q < P.rows * P.width) :
    frameGatherMemory memory P n (P.sourceAddress q) = memory (P.sourceAddress q) :=
  frameGatherMemory_input memory P hd n hn _ (P.sourceAddress_mem hP q hq)

theorem frameGatherMemory_output (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (q : ℕ) (hq : q < P.rows * P.width) :
    frameGatherMemory memory P (P.rows * P.width) (P.outputBase + q) =
      memory (P.sourceAddress q) := by simp [frameGatherMemory, hq]

#assert_trust kernel FrameGatherParameters.Valid.width_le
#assert_trust kernel FrameGatherParameters.column_lt
#assert_trust kernel FrameGatherParameters.sourceAddress_flat
#assert_trust kernel FrameGatherParameters.sourceAddress_mem
#assert_trust kernel frameGatherMemory_succ
#assert_trust kernel frameGatherMemory_input
#assert_trust kernel frameGatherMemory_read
#assert_trust kernel frameGatherMemory_output
#print axioms frameGatherMemory_read
end NLA.Proofs.TR04
