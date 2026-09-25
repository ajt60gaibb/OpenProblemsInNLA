import Mathlib

noncomputable section

/-!
IE-21 definitions.  This file deliberately separates the statement layer from
the proof layer: the spherical-row law and the asymptotic theorem remain
explicit hypotheses in `Challenge.lean` until the corresponding probability
and Haar-sphere infrastructure is imported.
-/

set_option autoImplicit false

namespace IE21

abbrev Matrix (m n : ℕ) := _root_.Matrix (Fin m) (Fin n) ℝ

instance matrixMeasurableSpace (m n : ℕ) : MeasurableSpace (Matrix m n) := ⊤

def l2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, (x i) ^ 2

def rowValue {m n : ℕ} (A : Matrix m n) (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  ∑ j, A i j * x j

def rowEnergy {m n : ℕ} (A : Matrix m n) (S : Finset (Fin m))
    (x : Fin n → ℝ) : ℝ := ∑ i ∈ S, (rowValue A i x) ^ 2

def kRows (theta : ℝ) (m : ℕ) : ℕ := ⌊theta * m⌋₊

/- The infimum formulation is the variational least singular value squared.
   It retains the exact floor convention and includes the zero-kernel case. -/
def sThetaSq (theta : ℝ) {m n : ℕ} (A : Matrix m n) : ℝ :=
  sInf {z : ℝ | ∃ S : Finset (Fin m), S.card = kRows theta m ∧
    ∃ x : Fin n → ℝ, l2Sq x = 1 ∧ z = rowEnergy A S x}

def opNormSq {m n : ℕ} (A : Matrix m n) : ℝ :=
  sSup {z : ℝ | ∃ x : Fin n → ℝ, l2Sq x = 1 ∧
    z = ∑ i, (rowValue A i x) ^ 2}

def gaussianH (theta : ℝ) (a : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * ∫ t in (-a)..a, t ^ 2 * Real.exp (-(t ^ 2) / 2)

def GaussianQuantile (theta a : ℝ) : Prop :=
  0 < a ∧ theta = (∫ t in (-a)..a, (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(t ^ 2) / 2))

def row {m n : ℕ} (A : Matrix m n) (i : Fin m) : Fin n → ℝ := fun j => A i j

def SphereSupported {m n : ℕ} (μ : MeasureTheory.Measure (Matrix m n)) : Prop :=
  ∀ i : Fin m, μ {A | l2Sq (row A i) = 1} = 1

def RowsIndependent {m n : ℕ} (μ : MeasureTheory.Measure (Matrix m n)) : Prop :=
  ∀ S : Finset (Fin m), ∀ E : Fin m → Set (Fin n → ℝ),
    μ {A | ∀ i ∈ S, row A i ∈ E i} = ∏ i ∈ S, μ {A | row A i ∈ E i}

/- The semantic law record keeps the sphere support and row-independence clauses
   visible. Replacing `SphereSupported` by normalized Hausdorff surface measure
   is the remaining probability-infrastructure task. -/
structure SphericalRowLaw {m n : ℕ} (μ : MeasureTheory.Measure (Matrix m n)) : Prop where
  row_uniform_on_sphere : SphereSupported μ
  rows_independent : RowsIndependent μ

structure SequenceData where
  m : ℕ → ℕ
  n : ℕ → ℕ
  μ : ∀ j, MeasureTheory.Measure (Matrix (m j) (n j))
  positive_m : ∀ j, 0 < m j
  positive_n : ∀ j, 0 < n j
  n_tendsto : Filter.Tendsto (fun j => (n j : ℝ)) Filter.atTop Filter.atTop
  aspect_tendsto : Filter.Tendsto (fun j => (m j : ℝ) / n j) Filter.atTop Filter.atTop
  spherical : ∀ j, SphericalRowLaw (μ j)

def ProbLimit (D : SequenceData) (f : ∀ j, Matrix (D.m j) (D.n j) → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Filter.Tendsto (fun j => D.μ j {A | |f j A - c| ≥ ε}) Filter.atTop (nhds 0)

def ratioValue (theta : ℝ) (D : SequenceData) (j : ℕ)
    (A : Matrix (D.m j) (D.n j)) : ℝ :=
  sThetaSq theta A / opNormSq A

end IE21
