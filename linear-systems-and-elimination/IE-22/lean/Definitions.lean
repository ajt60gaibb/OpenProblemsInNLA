import Mathlib

noncomputable section

/-! IE-22 statement layer. -/

set_option autoImplicit false

namespace IE22

abbrev Matrix (m n : ℕ) := _root_.Matrix (Fin m) (Fin n) ℝ

instance matrixMeasurableSpace (m n : ℕ) : MeasurableSpace (Matrix m n) := ⊤

def l2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, (x i) ^ 2

def rowValue {m n : ℕ} (A : Matrix m n) (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  ∑ j, A i j * x j

def rowEnergy {m n : ℕ} (A : Matrix m n) (S : Finset (Fin m))
    (x : Fin n → ℝ) : ℝ := ∑ i ∈ S, (rowValue A i x) ^ 2

def kRows (theta : ℝ) (m : ℕ) : ℕ := ⌊theta * m⌋₊

def sThetaSq (theta : ℝ) {m n : ℕ} (A : Matrix m n) : ℝ :=
  sInf {z : ℝ | ∃ S : Finset (Fin m), S.card = kRows theta m ∧
    ∃ x : Fin n → ℝ, l2Sq x = 1 ∧ z = rowEnergy A S x}

def unitRows {m n : ℕ} (A : Matrix m n) : Prop :=
  ∀ i : Fin m, l2Sq (fun j => A i j) = 1

def gaussianH (theta a : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * ∫ t in (-a)..a, t ^ 2 * Real.exp (-(t ^ 2) / 2)

def GaussianQuantile (theta a : ℝ) : Prop :=
  0 < a ∧ theta = (∫ t in (-a)..a, (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(t ^ 2) / 2))

def cTheta (theta a : ℝ) : ℝ := Real.sqrt (gaussianH theta a)

def M (theta : ℝ) (m n : ℕ) : ℝ :=
  sSup {z : ℝ | ∃ A : Matrix m n, unitRows A ∧
    z = Real.sqrt ((n : ℝ) / m) * Real.sqrt (sThetaSq theta A)}

def EventualUniformUpper (theta c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N R : ℕ, ∀ n m : ℕ, 0 < n → 0 < m →
    N ≤ n → R * n ≤ m → M theta m n ≤ c + ε

def NoSmallerUniformConstant (theta c : ℝ) : Prop :=
  ∀ c' : ℝ, c' < c → ¬ EventualUniformUpper theta c'

def SupremumConverges (theta c : ℝ) : Prop :=
  ∀ (m n : ℕ → ℕ),
    (∀ j, 0 < n j) → (∀ j, 0 < m j) →
    Filter.Tendsto (fun j => (m j : ℝ) / n j) Filter.atTop Filter.atTop →
    Filter.Tendsto (fun j : ℕ => M theta (m j) (n j)) Filter.atTop (nhds c)

end IE22
