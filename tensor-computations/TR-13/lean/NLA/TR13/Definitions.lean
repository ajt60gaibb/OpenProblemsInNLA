import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Coordinate definitions for the original TR-13 target

Tensor entries use zero-based indices. Border decompositions may approach through
the entire tensor space; only symmetric border decompositions restrict their
summands. A single nonzero polynomial describes the eventual Zariski-open set.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace NLA.TR13

abbrev Tensor (m n : ℕ) := (Fin m → Fin n) → ℂ
abbrev Moments (m n : ℕ) := Fin (m * (n - 1) + 1) → ℂ

def pureTensor {m n : ℕ} (v : Fin m → Fin n → ℂ) : Tensor m n :=
  fun i => ∏ j, v j (i j)

def symmetricTensor {m n : ℕ} (v : Fin n → ℂ) : Tensor m n :=
  pureTensor (fun _ => v)

/-- Homogeneous rational-normal-curve coordinates, including the node at infinity. -/
def vandermondeVector (n : ℕ) (a b : ℂ) : Fin n → ℂ :=
  fun i => a ^ (n - 1 - i.val) * b ^ i.val

def OrdinaryRankAtMost {m n : ℕ} (q : ℕ) (T : Tensor m n) : Prop :=
  ∃ v : Fin q → Fin m → Fin n → ℂ,
    T = ∑ j, pureTensor (v j)

def SymmetricRankAtMost {m n : ℕ} (q : ℕ) (T : Tensor m n) : Prop :=
  ∃ (c : Fin q → ℂ) (v : Fin q → Fin n → ℂ),
    T = ∑ j, c j • symmetricTensor (v j)

def VandermondeRankAtMost {m n : ℕ} (q : ℕ) (T : Tensor m n) : Prop :=
  ∃ (c a b : Fin q → ℂ), (∀ j, (a j, b j) ≠ (0, 0)) ∧
    T = ∑ j, c j • symmetricTensor (vandermondeVector n (a j) (b j))

def OrdinaryBorderRankAtMost {m n : ℕ} (q : ℕ) (T : Tensor m n) : Prop :=
  ∃ U : ℕ → Tensor m n,
    (∀ k, OrdinaryRankAtMost q (U k)) ∧ Tendsto U atTop (nhds T)

def SymmetricBorderRankAtMost {m n : ℕ} (q : ℕ) (T : Tensor m n) : Prop :=
  ∃ U : ℕ → Tensor m n,
    (∀ k, SymmetricRankAtMost q (U k)) ∧ Tendsto U atTop (nhds T)

def ordinaryRank {m n : ℕ} (T : Tensor m n) : ℕ :=
  sInf {q | OrdinaryRankAtMost q T}

def symmetricRank {m n : ℕ} (T : Tensor m n) : ℕ :=
  sInf {q | SymmetricRankAtMost q T}

def vandermondeRank {m n : ℕ} (T : Tensor m n) : ℕ :=
  sInf {q | VandermondeRankAtMost q T}

def ordinaryBorderRank {m n : ℕ} (T : Tensor m n) : ℕ :=
  sInf {q | OrdinaryBorderRankAtMost q T}

def symmetricBorderRank {m n : ℕ} (T : Tensor m n) : ℕ :=
  sInf {q | SymmetricBorderRankAtMost q T}

def hankel {m n : ℕ} (h : Moments m n) : Tensor m n :=
  fun i => h ⟨∑ j, (i j).val, by
    have hb : (∑ j : Fin m, (i j).val) ≤ m * (n - 1) := by
      calc
        (∑ j : Fin m, (i j).val) ≤ ∑ _j : Fin m, (n - 1) :=
          Finset.sum_le_sum (fun j _ => Nat.le_pred_of_lt (i j).isLt)
        _ = m * (n - 1) := by simp
    omega⟩

/-- Ceiling of `(m * (n - 1) + 1) / 2`. -/
def expectedRank (m n : ℕ) : ℕ := (m * (n - 1) + 2) / 2

def AllRanksEqual {m n : ℕ} (T : Tensor m n) (r : ℕ) : Prop :=
  ordinaryRank T = r ∧ symmetricRank T = r ∧
  ordinaryBorderRank T = r ∧ symmetricBorderRank T = r ∧
  vandermondeRank T = r

/-- An explicit principal Zariski-open subset of the finite affine moment space. -/
def principalOpen {m n : ℕ} (p : MvPolynomial (Fin (m * (n - 1) + 1)) ℂ) :
    Set (Moments m n) :=
  {h | MvPolynomial.eval h p ≠ 0}

end NLA.TR13
