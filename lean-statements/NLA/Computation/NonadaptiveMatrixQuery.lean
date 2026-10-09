import Mathlib
import NLA.Computation.SVDMachine

/-! Shared exact-real matrix query operations for RE-06 and related finite-family
sketching targets. Every oracle call is an element of a precommitted query list;
postprocessing sees only the stored transcript. Exact SVD is the canonical
arithmetic primitive, not an arbitrary result or cost oracle. -/
set_option autoImplicit false

open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Classical

namespace NLA.Computation.NonadaptiveMatrixQuery

/-- An ordered, duplicate-free enumeration of a family of size `m+2`. -/
abbrev Family (n m : ℕ) := Fin (m + 2) → Matrix (Fin n) (Fin n) ℝ

inductive Side where
  | right
  | left
  deriving DecidableEq

structure Query (n : ℕ) where
  side : Side
  vector : Fin n → ℝ

/-- The only operation allowed to read the unknown matrix. Each call to this
function is one matrix-vector query, on either side. -/
def answer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q : Query n) : Fin n → ℝ :=
  match q.side with
  | .right => fun i => ∑ j, A i j * q.vector j
  | .left => fun i => ∑ j, A j i * q.vector j

def standardBasis {n : ℕ} (j : Fin n) : Fin n → ℝ :=
  fun i => if i = j then 1 else 0

/-- An explicit plan contains no matrix `A` or oracle answer. `full=true`
selects the exact-recovery branch; the three blocks otherwise determine
every vector and both query sides before an answer is returned. -/
structure Plan (n : ℕ) where
  full : Bool
  s : ℕ
  k : ℕ
  ell : ℕ
  G0 : Matrix (Fin n) (Fin s) ℝ
  G1 : Matrix (Fin n) (Fin k) ℝ
  H : Matrix (Fin n) (Fin ell) ℝ

def queryList {n : ℕ} (P : Plan n) : List (Query n) :=
  if P.full then
    (List.finRange n).map (fun j => ⟨.right, standardBasis j⟩)
  else
    (List.finRange P.s).map (fun j => ⟨.right, fun i => P.G0 i j⟩) ++
    (List.finRange P.k).map (fun j => ⟨.right, fun i => P.G1 i j⟩) ++
    (List.finRange P.ell).map (fun j => ⟨.left, fun i => P.H i j⟩)

/-- Independent standard Gaussians indexed by a countable stream. Disjoint
index blocks in `makePlan` supply the three mutually independent sketches. -/
noncomputable def GaussianLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure GaussianLaw := by
  unfold GaussianLaw
  infer_instance

/-- Source parameters. `Nat.clog` and integer square root implement the two
integer ceilings by finite comparisons; the remaining real ceilings can be
implemented by increment-and-compare loops in the exact-real model. -/
def logWidth (m : ℕ) : ℕ := Nat.clog 2 (2 * (m + 2))

def rootWidth (m : ℕ) : ℕ :=
  let L := logWidth m
  let q := Nat.sqrt L
  if q ^ 2 < L then q + 1 else q

noncomputable def firstWidth (m : ℕ) (ε : ℝ) : ℕ :=
  let L := logWidth m
  let r := rootWidth m
  let η := ε / 4
  Nat.ceil (32 * (L : ℝ) / ((r : ℝ) * η) + 64 / η ^ 2)

noncomputable def secondWidth (m : ℕ) (ε : ℝ) : ℕ :=
  let r := rootWidth m
  let η := ε / 4
  r + 1 + Nat.ceil (256 * (r : ℝ) / η)

noncomputable def thirdWidth (m : ℕ) (ε : ℝ) : ℕ :=
  let k := secondWidth m ε
  let η := ε / 4
  k + 1 + Nat.ceil (256 * (k : ℝ) / η)

/-- No input matrix or previous answer enters this construction. The first
block uses unscaled standard Gaussians; dividing every squared warm-start
score by `s` would give precisely the source's normalized block and the
same minimizer. -/
noncomputable def makePlan (n m : ℕ) (ε : ℝ) (ω : ℕ → ℝ) : Plan n :=
  let s := firstWidth m ε
  let k := secondWidth m ε
  let ell := thirdWidth m ε
  if n ≤ s + k + ell then
    { full := true, s := 0, k := 0, ell := 0,
      G0 := 0, G1 := 0, H := 0 }
  else
    { full := false, s := s, k := k, ell := ell,
      G0 := fun i j => ω (j.val * n + i.val),
      G1 := fun i j => ω ((s + j.val) * n + i.val),
      H := fun i j => ω ((s + k + j.val) * n + i.val) }

/-- Oracle calls occur only on the committed list, in order. The resulting
list is the entire transcript passed into postprocessing. -/
def oracleAnswers {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Plan n) : List (Fin n → ℝ) :=
  (queryList P).map (answer A)

/-- A missing response has a defined zero value, making postprocessing total
even on malformed transcripts. Actual oracle transcripts have the right size. -/
def storedVector {n : ℕ} (responses : List (Fin n → ℝ)) (j : ℕ) : Fin n → ℝ :=
  (responses[j]?).getD (fun _ => 0)

/-- Finite deterministic scan, retaining the first index in a tie. -/
noncomputable def minimumIndex {m : ℕ} (score : Fin (m + 2) → ℝ) : Fin (m + 2) :=
  (List.finRange (m + 2)).foldl
    (fun best j => if score j < score best then j else best) 0

noncomputable def squaredFrobenius {a b : ℕ}
    (X Y : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  ∑ i, ∑ j, (X i j - Y i j) ^ 2

noncomputable def frobenius {a b : ℕ}
    (X Y : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  Real.sqrt (squaredFrobenius X Y)

/-- The attained finite-family minimum, computed by the same finite scan.
This definition is for the target predicate, not an input to the algorithm. -/
noncomputable def optimum {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (F : Family n m) : ℝ :=
  frobenius A (F (minimumIndex (fun j => squaredFrobenius A (F j))))

/-- The complete data returned by one exact full-SVD primitive. -/
structure SVDResult (a b : ℕ) where
  U : Matrix (Fin a) (Fin a) ℝ
  sigma : Fin (min a b) → ℝ
  V : Matrix (Fin b) (Fin b) ℝ

def ValidSVDResult {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (R : SVDResult a b) : Prop :=
  NLA.Computation.SVDMachine.ValidSVD B R.U R.sigma R.V

/-- Exact SVD is a primitive of the canonical exact-real model. The fallback
keeps the operation total if called outside its mathematically valid domain;
`ValidSVDResult` fixes the meaning of the chosen primitive response. -/
noncomputable def exactSVD {a b : ℕ}
    (B : Matrix (Fin a) (Fin b) ℝ) : SVDResult a b :=
  if h : ∃ R : SVDResult a b, ValidSVDResult B R then
    Classical.choose h
  else
    ⟨0, fun _ => 0, 0⟩

/-- Moore–Penrose inverse, formed by one exact SVD and reciprocal positive
singular values; zero singular values contribute zero. This is defined for
rank-deficient and zero matrices too. -/
noncomputable def pseudoInverse {a b : ℕ}
    (B : Matrix (Fin a) (Fin b) ℝ) : Matrix (Fin b) (Fin a) ℝ :=
  let R := exactSVD B
  fun i j => ∑ t : Fin (min a b),
    R.V i ⟨t.val, lt_of_lt_of_le t.isLt (Nat.min_le_right a b)⟩ *
      (if R.sigma t = 0 then 0 else (R.sigma t)⁻¹) *
      R.U j ⟨t.val, lt_of_lt_of_le t.isLt (Nat.min_le_left a b)⟩

/-- The source's low-rank repair can equivalently be written
`Y (HᵀY)† W` whenever `Hᵀ` has full rank on `range(Y)`, which holds almost
surely in the nontrivial Gaussian branch. Unlike a dynamic-rank basis, this
fixed-dimension SVD formula also defines every exceptional outcome. -/
noncomputable def postprocess {n m : ℕ} (F : Family n m)
    (P : Plan n) (responses : List (Fin n → ℝ)) : Fin (m + 2) :=
  if P.full then
    let recovered : Matrix (Fin n) (Fin n) ℝ :=
      fun i j => storedVector responses j.val i
    minimumIndex (fun b => squaredFrobenius recovered (F b))
  else
    let Z0 : Matrix (Fin n) (Fin P.s) ℝ :=
      fun i j => storedVector responses j.val i
    let Z1 : Matrix (Fin n) (Fin P.k) ℝ :=
      fun i j => storedVector responses (P.s + j.val) i
    let ZH : Matrix (Fin n) (Fin P.ell) ℝ :=
      fun i j => storedVector responses (P.s + P.k + j.val) i
    let b0 := minimumIndex (fun b => squaredFrobenius Z0 (F b * P.G0))
    let Y := Z1 - F b0 * P.G1
    let W := ZH.transpose - P.H.transpose * F b0
    let S := P.H.transpose * Y
    let repaired := F b0 + Y * pseudoInverse S * W
    minimumIndex (fun b => squaredFrobenius repaired (F b))

/-- The same fully specified procedure serves every dimension, family,
accuracy, and unknown matrix. Its output is always a member of `F`. -/
noncomputable def run {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (ω : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let P := makePlan n m ε ω
  F (postprocess F P (oracleAnswers A P))

def QueryBound (n m : ℕ) (ε C : ℝ) (b : ℕ) : Prop :=
  ∀ ω : ℕ → ℝ,
    ((queryList (makePlan n m ε ω)).length : ℝ) ≤
      C * Real.sqrt (Real.log (2 * (m + 2 : ℕ))) * ε⁻¹ ^ 2 *
        (1 + Real.log (2 + Real.log (2 * (m + 2 : ℕ))) +
          Real.log (1 / ε)) ^ b

def Successful {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) : Prop :=
  GaussianLaw {ω | frobenius A (run F A ε ω) ≤ (3 + ε) * optimum A F} ≥
    (99 / 100 : ENNReal)

/-- SVD availability is included as an affirmative fact, not a premise of
the success guarantee; the primitive has no unconstrained output oracle. -/
def SVDTotal : Prop :=
  ∀ (a b : ℕ) (B : Matrix (Fin a) (Fin b) ℝ),
    ValidSVDResult B (exactSVD B)


end NLA.Computation.NonadaptiveMatrixQuery
