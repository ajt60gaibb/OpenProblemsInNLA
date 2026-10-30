import Mathlib
import NLA.Computation.NonadaptiveMatrixQuery

/-! Concrete exact-real query procedure for RE-05. All matrix-dependent data
enter through actual responses to a precommitted finite list of left/right
queries. Finite scans, Gram--Schmidt, Gaussian draws and exact SVD are free
arithmetic in the canonical query-only model. -/
set_option autoImplicit false

open scoped BigOperators
open Classical

namespace NLA.Computation.LinearFamilyQuery

open NLA.Computation.NonadaptiveMatrixQuery

abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Basis (n q : ℕ) := Fin (q + 1) → Square n

/-- Concrete linear independence of the explicitly supplied basis. -/
def Independent {n q : ℕ} (P : Basis n q) : Prop :=
  ∀ c : Fin (q + 1) → ℝ,
    (∀ i j : Fin n, (∑ h, c h * P h i j) = 0) →
      ∀ h, c h = 0

def represent {n q : ℕ} (P : Basis n q)
    (c : Fin (q + 1) → ℝ) : Square n :=
  fun i j => ∑ h, c h * P h i j

noncomputable def inner {n : ℕ} (X Y : Square n) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j

noncomputable def norm (n : ℕ) (X : Square n) : ℝ :=
  Real.sqrt (inner X X)

/-- Literal finite Gram--Schmidt in the supplied order. Zero residuals have
a defined zero output; independence rules them out on admissible inputs. -/
noncomputable def orthonormalList {n q : ℕ} (P : Basis n q) : List (Square n) :=
  (List.finRange (q + 1)).foldl (fun accepted j =>
    let v : Square n := fun i k =>
      P j i k - ∑ E ∈ accepted.toFinset, inner (P j) E * E i k
    let scale := norm n v
    accepted ++ [if scale = 0 then (0 : Square n) else (fun i k => v i k / scale)]) []

noncomputable def orthonormalMember {n q : ℕ} (P : Basis n q)
    (j : Fin (q + 1)) : Square n :=
  (orthonormalList P)[j.val]?.getD 0

/-- The known-family left leverage matrix `R=∑ E_j E_jᵀ`. -/
noncomputable def leverage {n q : ℕ} (P : Basis n q) : Square n :=
  fun i k => ∑ j : Fin (q + 1), ∑ h : Fin n,
    orthonormalMember P j i h * orthonormalMember P j k h

/-- The source's squared-error parameter and spectral-split widths. -/
noncomputable def squaredAccuracy (ε : ℝ) : ℝ := ε / 9

noncomputable def baseWidth (q : ℕ) (ξ : ℝ) : ℝ :=
  16 * Real.log (20 * (q + 1 : ℕ)) + 160 / ξ

noncomputable def threshold (q : ℕ) (ξ : ℝ) : ℝ :=
  Real.sqrt ((q + 1 : ℕ) / baseWidth q ξ)

noncomputable def gaussianWidth (q : ℕ) (ξ : ℝ) : ℕ :=
  Nat.ceil (8 * Real.log (20 * (q + 1 : ℕ)) +
    threshold q ξ * baseWidth q ξ)

/-- One nonadaptive plan. `U` is an exact SVD of the known PSD leverage
matrix; only positive singular vectors with value above the threshold are
queried on the left. The right block uses independent standard Gaussians. -/
structure Plan (n : ℕ) where
  selected : List (Fin n)
  U : Square n
  s : ℕ
  G : Matrix (Fin n) (Fin s) ℝ

noncomputable def makePlan {n q : ℕ} (P : Basis n q)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) : Plan n :=
  let R := exactSVD (leverage P)
  let t := threshold q ξ
  let s := gaussianWidth q ξ
  { selected := (List.finRange n).filter
      (fun j => t < R.sigma (Fin.cast (Nat.min_self n).symm j))
    U := R.U
    s := s
    G := fun i j => ω ((copy.val * s + j.val) * n + i.val) }

def queries {n : ℕ} (plan : Plan n) : List (Query n) :=
  plan.selected.map (fun h => ⟨.left, fun i => plan.U i h⟩) ++
    (List.finRange plan.s).map (fun j => ⟨.right, fun i => plan.G i j⟩)

noncomputable def plans {n q : ℕ} (P : Basis n q)
    (ε : ℝ) (ω : ℕ → ℝ) : Fin 15 → Plan n :=
  fun copy => makePlan P (squaredAccuracy ε) ω copy

def batchQueries {n : ℕ} (schedule : Fin 15 → Plan n) : List (Query n) :=
  (List.finRange 15).flatMap (fun copy => queries (schedule copy))

/-- One query for each member of `batchQueries`, on the specified side. -/
def batchAnswers {n : ℕ} (A : Square n) (schedule : Fin 15 → Plan n) :
    List (Fin n → ℝ) :=
  (batchQueries schedule).map (answer A)

noncomputable def dot {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, x i * y i

def uColumn {n : ℕ} (plan : Plan n) (h : Fin plan.selected.length) : Fin n → ℝ :=
  fun i => plan.U i plan.selected[h]

/-- Orthogonal complement of the selected left singular subspace. -/
noncomputable def complement {n : ℕ} (plan : Plan n) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i - ∑ h : Fin plan.selected.length,
    dot (uColumn plan h) x * uColumn plan h i

noncomputable def predictedLeft {n q : ℕ} (P : Basis n q)
    (plan : Plan n) (j : Fin (q + 1))
    (h : Fin plan.selected.length) : Fin n → ℝ :=
  fun c => ∑ i, P j i c * uColumn plan h i

noncomputable def predictedRight {n q : ℕ} (P : Basis n q)
    (plan : Plan n) (j : Fin (q + 1)) (g : Fin plan.s) : Fin n → ℝ :=
  fun i => ∑ c, P j i c * plan.G c g

def observedLeft {n : ℕ} (plan : Plan n)
    (responses : List (Fin n → ℝ))
    (h : Fin plan.selected.length) : Fin n → ℝ :=
  storedVector responses h.val

def observedRight {n : ℕ} (plan : Plan n)
    (responses : List (Fin n → ℝ)) (g : Fin plan.s) : Fin n → ℝ :=
  storedVector responses (plan.selected.length + g.val)

/-- Exact Gram matrix for the source's measured-left plus projected-right
least-squares objective, in the original supplied basis. The reciprocal `1/s`
is defined even for malformed zero-width plans. -/
noncomputable def gram {n q : ℕ} (P : Basis n q)
    (plan : Plan n) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
  fun j k =>
    (∑ h : Fin plan.selected.length,
      dot (predictedLeft P plan j h) (predictedLeft P plan k h)) +
    (1 / (plan.s : ℝ)) *
      ∑ g : Fin plan.s,
        dot (complement plan (predictedRight P plan j g))
            (complement plan (predictedRight P plan k g))

noncomputable def rhs {n q : ℕ} (P : Basis n q)
    (plan : Plan n) (responses : List (Fin n → ℝ)) : Fin (q + 1) → ℝ :=
  fun j =>
    (∑ h : Fin plan.selected.length,
      dot (predictedLeft P plan j h) (observedLeft plan responses h)) +
    (1 / (plan.s : ℝ)) *
      ∑ g : Fin plan.s,
        dot (complement plan (predictedRight P plan j g))
            (complement plan (observedRight plan responses g))

/-- The exact Moore--Penrose solve returns a coefficient vector even when
the sketched Gram matrix is singular. It is the deterministic minimum
coefficient-norm least-squares minimizer in the input basis. -/
noncomputable def singleOutput {n q : ℕ} (P : Basis n q)
    (plan : Plan n) (responses : List (Fin n → ℝ)) : Fin (q + 1) → ℝ :=
  let Ginv := pseudoInverse (gram P plan)
  let b := rhs P plan responses
  fun j => ∑ k, Ginv j k * b k

def responseOffset {n : ℕ} (schedule : Fin 15 → Plan n)
    (copy : Fin 15) : ℕ :=
  ∑ prior : Fin 15, if prior < copy then (queries (schedule prior)).length else 0

def copyResponses {n : ℕ} (schedule : Fin 15 → Plan n)
    (responses : List (Fin n → ℝ)) (copy : Fin 15) : List (Fin n → ℝ) :=
  (responses.drop (responseOffset schedule copy)).take (queries (schedule copy)).length

noncomputable def copyOutput {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (copy : Fin 15) : Fin (q + 1) → ℝ :=
  singleOutput P (schedule copy) (copyResponses schedule responses copy)

noncomputable def coefficientDistance {n q : ℕ} (P : Basis n q)
    (x y : Fin (q + 1) → ℝ) : ℝ :=
  frobenius (represent P x) (represent P y)

/-- Median of all fifteen coefficient distances, including self-distance. -/
noncomputable def medianRadius {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (copy : Fin 15) : ℝ :=
  let scores := ((List.finRange 15).map fun other =>
    coefficientDistance P (copyOutput P schedule responses copy)
      (copyOutput P schedule responses other)).mergeSort (· ≤ ·)
  scores[7]?.getD 0

/-- The source's median-radius selector, with first-index tie breaking. -/
noncomputable def chooseCopy {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ)) : Fin 15 :=
  (List.finRange 15).foldl
    (fun best copy =>
      if medianRadius P schedule responses copy <
          medianRadius P schedule responses best then copy else best) 0

/-- All arithmetic after the query batch uses only the known basis, the
committed schedule, and stored responses. -/
noncomputable def postprocess {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ)) :
    Fin (q + 1) → ℝ :=
  copyOutput P schedule responses (chooseCopy P schedule responses)

noncomputable def run {n q : ℕ} (P : Basis n q) (A : Square n)
    (ε : ℝ) (ω : ℕ → ℝ) : Fin (q + 1) → ℝ :=
  let schedule := plans P ε ω
  postprocess P schedule (batchAnswers A schedule)

noncomputable def optimum {n q : ℕ} (P : Basis n q) (A : Square n) : ℝ :=
  sInf {r : ℝ | ∃ c : Fin (q + 1) → ℝ, r = frobenius A (represent P c)}

end NLA.Computation.LinearFamilyQuery
