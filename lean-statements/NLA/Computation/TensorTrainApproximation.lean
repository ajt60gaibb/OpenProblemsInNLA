import NLA.Computation.SVDMachine
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Concrete tensor-train format, unfolding ranks, mixed-radix input/output and
optimal-error semantics shared by the live and frozen TR-04 boundaries. -/
set_option autoImplicit false
open scoped BigOperators

namespace NLA.Computation.TensorTrainApproximation
open NLA.Computation.SVDMachine

/-- The full original tensor-format domain. -/
structure Shape where
  order : ℕ
  order_ge : 3 ≤ order
  mode : Fin order → ℕ
  mode_ge : ∀ i, 2 ≤ mode i

abbrev Index (S : Shape) := (i : Fin S.order) → Fin (S.mode i)
abbrev Tensor (S : Shape) := Index S → ℝ
abbrev Cut (S : Shape) := Fin (S.order - 1)
abbrev Ranks (S : Shape) := Cut S → ℕ

abbrev RowIndex (S : Shape) (j : Cut S) :=
  (i : {i : Fin S.order // i.val ≤ j.val}) → Fin (S.mode i.1)
abbrev ColIndex (S : Shape) (j : Cut S) :=
  (i : {i : Fin S.order // j.val < i.val}) → Fin (S.mode i.1)

/-- Each mode occurs in exactly one side of the actual prescribed cut. -/
def join (S : Shape) (j : Cut S) (a : RowIndex S j) (b : ColIndex S j) : Index S :=
  fun i => if h : i.val ≤ j.val then a ⟨i, h⟩ else b ⟨i, Nat.lt_of_not_ge h⟩

def Unfold (S : Shape) (Y : Tensor S) (j : Cut S) :
    Matrix (RowIndex S j) (ColIndex S j) ℝ :=
  fun a b => Y (join S j a b)

/-- Actual real matrix rank, with no consistency restriction on positive ranks. -/
def Feasible (S : Shape) (r : Ranks S) (Y : Tensor S) : Prop :=
  ∀ j, Matrix.rank (Unfold S Y j) ≤ r j

noncomputable def FrobeniusSq (S : Shape) (A Y : Tensor S) : ℝ :=
  ∑ a : Index S, (A a - Y a)^2

/-- The genuine infimum of all feasible squared errors. Zero is feasible;
finite-dimensional closed rank constraints make this the attained minimum. -/
noncomputable def Optimum (S : Shape) (r : Ranks S) (A : Tensor S) : ℝ :=
  sInf {e : ℝ | ∃ Y : Tensor S, Feasible S r Y ∧ e = FrobeniusSq S A Y}

def DenseSize (S : Shape) : ℕ := ∏ i, S.mode i

/-- Last-index-fastest mixed-radix weights. -/
def SuffixSize (S : Shape) (i : Fin S.order) : ℕ :=
  ∏ s ∈ Finset.univ.filter (fun s : Fin S.order => i < s), S.mode s

def Offset (S : Shape) (a : Index S) : ℕ :=
  ∑ i, (a i).val * SuffixSize S i

/-- Fixed input placement only: this is not an executable digit-extraction opcode. -/
def Decode (S : Shape) (offset : ℕ) : Index S :=
  fun i => ⟨(offset / SuffixSize S i) % S.mode i,
    Nat.mod_lt _ (lt_of_lt_of_le (by decide : 0 < 2) (S.mode_ge i))⟩

/-- The store contains mode sizes, ranks, and every dense tensor entry, with
no optimal tensor, rank table or error oracle included. -/
def InputMemory (S : Shape) (r : Ranks S) (A : Tensor S) (address : ℕ) : ℝ :=
  if hn : address < S.order then (S.mode ⟨address, hn⟩ : ℝ)
  else if hr : address - S.order < S.order - 1 then
    (r ⟨address - S.order, hr⟩ : ℝ)
  else if address - (2 * S.order - 1) < DenseSize S then
    A (Decode S (address - (2 * S.order - 1)))
  else 0

def Start (P : Program) (S : Shape) (r : Ranks S) (A : Tensor S) : State P :=
  initial P S.order (InputMemory S r A)

/-- A successful pointer reads exactly the original N-entry tensor shape.
The standard mixed-radix Offset enumerates all its entries bijectively. -/
def Returns (P : Program) (S : Shape) (s : State P) (X : Tensor S) : Prop :=
  ∃ base : ℕ, s.status = .halted base ∧
    ∀ a : Index S, X a = s.memory (base + Offset S a)

def Size (S : Shape) (r : Ranks S) : ℕ :=
  DenseSize S + S.order + (∑ j, r j) + 1

end NLA.Computation.TensorTrainApproximation
