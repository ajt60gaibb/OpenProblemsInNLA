import Mathlib
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! MI-16: the exact finite algebraic determination of the permanent maximum.
The complete source and pre-implementation specification are retained in
`docs/lean/statements/MI-16/`. This file states, but does not prove, the
all-spectrum result. In particular, the candidate polynomial and selector are
defined by finite polynomial, partition, permutation, and root operations. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open Classical

namespace NLA.Statements.MI16

/-- There are `d + 1` coordinates. The successor presentation makes each
deleted row and column a `Fin d` minor, including the one-by-one case. -/
abbrev Index (d : ℕ) := Fin (d + 1)

/-- `aᵢⱼ` and `z` are independent polynomial variables. -/
abbrev Variable (d : ℕ) := Sum (Index d × Index d) Unit
abbrev CoordinateRing (d : ℕ) (K : Type*) [Field K] :=
  MvPolynomial (Variable d) K

noncomputable def genericMatrix (d : ℕ) (K : Type*) [Field K] :
    Matrix (Index d) (Index d) (CoordinateRing d K) :=
  fun i j => MvPolynomial.X (.inl (i, j))

noncomputable def valueVariable (d : ℕ) (K : Type*) [Field K] : CoordinateRing d K :=
  MvPolynomial.X (.inr ())

/-- The source's transposed deleted-minor convention:
`C(A)ᵢⱼ = per(A with row j and column i deleted)`. -/
noncomputable def permanentalAdjoint (d : ℕ) (K : Type*) [Field K]
    (A : Matrix (Index d) (Index d) (CoordinateRing d K)) :
    Matrix (Index d) (Index d) (CoordinateRing d K) :=
  fun i j => (show Matrix (Fin d) (Fin d) (CoordinateRing d K) from
    fun r c => A (j.succAbove r) (i.succAbove c)).permanent

noncomputable def scalarMatrix (d : ℕ) (K : Type*) [Field K] (x : K) :
    Matrix (Index d) (Index d) (CoordinateRing d K) :=
  Matrix.diagonal (fun _ => MvPolynomial.C x)

/-- `qλ(A)`, with each distinct eigenvalue represented exactly once. The
factors commute because each is a polynomial in the same matrix. -/
noncomputable def spectralEquation (d : ℕ) (K : Type*) [Field K]
    (spectrum : Index d → K) :
    Matrix (Index d) (Index d) (CoordinateRing d K) :=
  ((List.ofFn spectrum).eraseDups).foldl
    (fun B θ => B * (genericMatrix d K - scalarMatrix d K θ)) 1

/-- The four complete families of specialized critical-locus equations. -/
noncomputable def criticalEquations (d : ℕ) (K : Type*) [Field K]
    (spectrum : Index d → K) : Set (CoordinateRing d K) :=
  {f | (∃ k : Index d,
          f = Matrix.trace ((genericMatrix d K) ^ (k.val + 1)) -
            MvPolynomial.C (∑ i, spectrum i ^ (k.val + 1))) ∨
       (∃ i j : Index d, f = spectralEquation d K spectrum i j) ∨
       (∃ i j : Index d,
          f = (genericMatrix d K * permanentalAdjoint d K (genericMatrix d K) -
            permanentalAdjoint d K (genericMatrix d K) * genericMatrix d K) i j) ∨
       f = valueVariable d K - (genericMatrix d K).permanent}

noncomputable def criticalIdeal (d : ℕ) (K : Type*) [Field K]
    (spectrum : Index d → K) : Ideal (CoordinateRing d K) :=
  Ideal.span (criticalEquations d K spectrum)

/-- Substitute the distinguished `z` variable into a univariate polynomial. -/
noncomputable def embedValuePolynomial (d : ℕ) (K : Type*) [Field K]
    (P : Polynomial K) : CoordinateRing d K :=
  P.eval₂ MvPolynomial.C (valueVariable d K)

/-- The actual exact coefficient field `ℚ(λ₁,…,λₙ)` inside `ℝ`. -/
noncomputable abbrev SpectrumField (d : ℕ) (spectrum : Index d → ℝ) :=
  IntermediateField.adjoin ℚ (Set.range spectrum)

noncomputable def eigenvalueInField (d : ℕ) (spectrum : Index d → ℝ)
    (i : Index d) : SpectrumField d spectrum :=
  ⟨spectrum i, IntermediateField.subset_adjoin ℚ (Set.range spectrum) (Set.mem_range_self i)⟩

/-- This is the monic generator of the radical of the specialized univariate
elimination ideal. The divisibility clause defines its full root set; there is
no free choice of a favorable critical-value polynomial. -/
noncomputable def IsCriticalValuePolynomial (d : ℕ) (spectrum : Index d → ℝ)
    (P : Polynomial (SpectrumField d spectrum)) : Prop :=
  P.Monic ∧ 0 < P.natDegree ∧ Squarefree P ∧
    ∀ Q : Polynomial (SpectrumField d spectrum),
      ((∃ k : ℕ, 0 < k ∧
          (embedValuePolynomial d (SpectrumField d spectrum) Q) ^ k ∈
            criticalIdeal d (SpectrumField d spectrum)
              (eigenvalueInField d spectrum)) ↔ P ∣ Q)

/-- Interpret the exact-field polynomial in the ordered real extension. -/
noncomputable def realCriticalPolynomial (d : ℕ) (spectrum : Index d → ℝ)
    (P : Polynomial (SpectrumField d spectrum)) : Polynomial ℝ :=
  P.map (algebraMap (SpectrumField d spectrum) ℝ)

/-- The original complex unitary orbit. -/
def IsUnitary (d : ℕ) (U : Matrix (Index d) (Index d) ℂ) : Prop :=
  U.conjTranspose * U = 1

noncomputable def orbitMatrix (d : ℕ) (spectrum : Index d → ℝ)
    (U : Matrix (Index d) (Index d) ℂ) :
    Matrix (Index d) (Index d) ℂ :=
  U.conjTranspose * Matrix.diagonal (fun i => (spectrum i : ℂ)) * U

/-- Complete homogeneous symmetric polynomial, evaluated as an explicitly
finite sum of monomials of total degree `j`. -/
noncomputable def homogeneous (d j : ℕ) (spectrum : Index d → ℝ) : ℝ :=
  ∑ a : Index d → Fin (j + 1),
    if (∑ i, (a i).val) = j then ∏ i, spectrum i ^ (a i).val else 0

/-- The Schur polynomial via Jacobi–Trudi, with zero for negative indices.
The partition's parts are sorted into decreasing order. -/
noncomputable def schur (d m : ℕ) (ν : Nat.Partition m)
    (spectrum : Index d → ℝ) : ℝ :=
  let parts := ν.parts.sort (· ≥ ·)
  let ℓ := parts.length
  Matrix.det (fun i j : Fin ℓ =>
    let degree : ℤ := (parts[i.val]!) - (i.val : ℤ) + (j.val : ℤ)
    if degree < 0 then 0 else homogeneous d degree.toNat spectrum)

/-- Mathlib's `cycleType` omits fixed points. Frobenius's character formula
uses the full cycle type, so we insert the missing one-cycles explicitly. -/
noncomputable def fullCycleLengths {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) : Multiset ℕ :=
  σ.cycleType + Multiset.replicate (Fintype.card α - σ.cycleType.sum) 1

noncomputable def powerSumPolynomial (m k : ℕ) : MvPolynomial (Fin m) ℤ :=
  ∑ i : Fin m, MvPolynomial.X i ^ k

noncomputable def alternant (m : ℕ) : MvPolynomial (Fin m) ℤ :=
  ∏ ij ∈ ((Finset.univ : Finset (Fin m × Fin m)).filter (fun ij => ij.1 < ij.2)),
    (MvPolynomial.X ij.1 - MvPolynomial.X ij.2)

/-- The irreducible symmetric-group character as Frobenius's finite
coefficient formula. It is a concrete integer polynomial coefficient,
including the one-cycles absent from Mathlib's `cycleType`. -/
noncomputable def character {α : Type*} [Fintype α] [DecidableEq α]
    (ν : Nat.Partition (Fintype.card α)) (σ : Equiv.Perm α) : ℤ :=
  let m := Fintype.card α
  let parts := ν.parts.sort (· ≥ ·)
  let exponent : Fin m →₀ ℕ :=
    ∑ i : Fin m, Finsupp.single i (parts[i.val]! + (m - 1 - i.val))
  MvPolynomial.coeff exponent
    (alternant m * ((fullCycleLengths σ).map (powerSumPolynomial m)).prod)

/-- Row permutations of the `p`-by-`d+1` tensor-position array. -/
def rowPermutation (d p : ℕ) (h : Fin p → Equiv.Perm (Index d)) :
    Equiv.Perm (Fin p × Index d) where
  toFun := fun x => (x.1, h x.1 x.2)
  invFun := fun x => (x.1, (h x.1).symm x.2)
  left_inv := by intro x; cases x; simp
  right_inv := by intro x; cases x; simp

/-- Column permutations of the same position array. -/
def columnPermutation (d p : ℕ) (k : Index d → Equiv.Perm (Fin p)) :
    Equiv.Perm (Fin p × Index d) where
  toFun := fun x => (k x.2 x.1, x.2)
  invFun := fun x => ((k x.2).symm x.1, x.2)
  left_inv := by intro x; cases x; simp
  right_inv := by intro x; cases x; simp

/-- The exact finite rational character sum, cast to reals for use in `T`.
There is no Haar integral or unevaluated limit in this definition. -/
noncomputable def momentWeight (d p : ℕ)
    (ν : Nat.Partition (Fintype.card (Fin p × Index d))) : ℝ :=
  let m := Fintype.card (Fin p × Index d)
  ((character ν (1 : Equiv.Perm (Fin p × Index d)) : ℝ) / (Nat.factorial m : ℝ)) *
    ∑ h : Fin p → Equiv.Perm (Index d),
      ∑ k : Index d → Equiv.Perm (Fin p),
        (character ν (columnPermutation d p k * rowPermutation d p h) : ℝ)

/-- Source Theorem 2.1's finite spectral moment: one Schur quotient for
each partition of all `p*(d+1)` positions with at most `d+1` rows. -/
noncomputable def spectralMoment (d p : ℕ) (spectrum : Index d → ℝ) : ℝ :=
  let m := Fintype.card (Fin p × Index d)
  ∑ ν : Nat.Partition m,
    if ν.parts.card ≤ d + 1 then
      momentWeight d p ν * schur d m ν spectrum /
        schur d m ν (fun _ => 1)
    else 0

/-- Maximum of the nonempty finite input list; it is not a maximum over
orbit matrices. -/
noncomputable def largestEigenvalue (d : ℕ) (spectrum : Index d → ℝ) : ℝ :=
  (Finset.univ.image spectrum).max' (by simp)

/-- Distinct real critical-value roots in the *closed* source interval,
ordered increasingly. An infeasible complex-orbit critical value is retained. -/
noncomputable def candidateRoots (P : Polynomial ℝ) (B : ℝ) : List ℝ :=
  ((P.roots.toFinset.filter (fun r => 0 ≤ r ∧ r ≤ B)).sort (· ≤ ·))

/-- In the multiple-root branch this fold is the minimum adjacent gap.
Its initial value `B` is at least every gap between roots in `[0,B]`. -/
noncomputable def rootGap (roots : List ℝ) (B : ℝ) : ℝ :=
  (List.range (roots.length - 1)).foldl
    (fun gap j => min gap (roots[j + 1]! - roots[j]!)) B

/-- Source Theorem 2.1's exact finite selector. `Nat.sInf` implements the
least qualifying `b`; Target also asserts the relevant set is nonempty. -/
noncomputable def spectralAnswer (d : ℕ) (spectrum : Index d → ℝ)
    (P : Polynomial ℝ) : ℝ :=
  let n := d + 1
  let B := (largestEigenvalue d spectrum) ^ n
  let roots := candidateRoots P B
  if ∀ i, spectrum i = 0 then 0
  else if roots.length ≤ 1 then roots.headD 0
  else
    let ρ := rootGap roots B
    let b := sInf {j : ℕ | (1 : ℝ) + 16 * (n : ℝ)^2 * B / ρ ≤ (2 : ℝ)^j}
    let h := Nat.ceil (4 * B / ρ)
    let p := 2 * n^2 * b * h
    roots.headD 0 +
      ∑ j ∈ Finset.range (roots.length - 1),
        (roots[j + 1]! - roots[j]!) *
          (if spectralMoment d p spectrum > (roots[j]!) ^ p then (1 : ℝ) else 0)

/-- The complete original exact-value determination for every nonnegative
spectrum. The explicit answer is *attained* and bounds every unitary orbit
matrix. Polynomial and denominator well-definedness are part of the target;
they are not hypotheses or opaque answer oracles. -/
def Target : Prop :=
  ∀ (d : ℕ) (spectrum : Index d → ℝ),
    (∀ i, 0 ≤ spectrum i) →
      ∃ P : Polynomial (SpectrumField d spectrum),
        IsCriticalValuePolynomial d spectrum P ∧
        (∀ (p : ℕ) (ν : Nat.Partition (Fintype.card (Fin p × Index d))),
          0 < p → ν.parts.card ≤ d + 1 →
            0 < schur d (Fintype.card (Fin p × Index d)) ν (fun _ => 1)) ∧
        (let B := (largestEigenvalue d spectrum) ^ (d + 1)
         let roots := candidateRoots (realCriticalPolynomial d spectrum P) B
         (∀ i, spectrum i = 0) ∨
           (roots ≠ [] ∧
            (roots.length ≤ 1 ∨
              (0 < rootGap roots B ∧
               ∃ j : ℕ,
                 (1 : ℝ) + 16 * ((d + 1 : ℕ) : ℝ)^2 * B / rootGap roots B ≤
                   (2 : ℝ)^j)))) ∧
        (∃ U : Matrix (Index d) (Index d) ℂ,
          IsUnitary d U ∧
          (orbitMatrix d spectrum U).permanent =
            (spectralAnswer d spectrum (realCriticalPolynomial d spectrum P) : ℂ)) ∧
        (∀ U : Matrix (Index d) (Index d) ℂ,
          IsUnitary d U →
            ((orbitMatrix d spectrum U).permanent).im = 0 ∧
            ((orbitMatrix d spectrum U).permanent).re ≤
              spectralAnswer d spectrum (realCriticalPolynomial d spectrum P))

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.MI16
