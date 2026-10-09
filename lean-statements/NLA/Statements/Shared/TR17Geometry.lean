import Mathlib

/-! Concrete coordinate algebra for the generic Euclidean distance critical scheme
of a Segre–Veronese cone. The quotient retains scheme multiplicities. -/

set_option autoImplicit false
open scoped BigOperators

namespace NLA.Statements.Shared.TR17Geometry

abbrev Coord (k : ℕ) (n d : Fin k → ℕ) :=
  ∀ j : Fin k, Sym (Fin (n j)) (d j)

abbrev Parameter (k : ℕ) (n : Fin k → ℕ) := Option (Σ j : Fin k, Fin (n j))

noncomputable def monomial (k : ℕ) (n d : Fin k → ℕ)
    (K : Type*) [Field K]
    (α : Coord k n d) : MvPolynomial (Parameter k n) K :=
  MvPolynomial.X none *
    ∏ j : Fin k,
      ((α j : Multiset (Fin (n j))).map
        (fun x => MvPolynomial.X (some ⟨j, x⟩))).prod

noncomputable def coneIdeal (k : ℕ) (n d : Fin k → ℕ)
    (K : Type*) [Field K] : Ideal (MvPolynomial (Coord k n d) K) :=
  RingHom.ker (MvPolynomial.aeval (monomial k n d K)).toRingHom

abbrev GenericField (k : ℕ) (n d : Fin k → ℕ) :=
  FractionRing (MvPolynomial (Coord k n d) ℂ)

noncomputable def genericData (k : ℕ) (n d : Fin k → ℕ)
    (α : Coord k n d) : GenericField k n d :=
  algebraMap (MvPolynomial (Coord k n d) ℂ) (GenericField k n d)
    (MvPolynomial.X α)

noncomputable def originIdeal (k : ℕ) (n d : Fin k → ℕ) :
    Ideal (MvPolynomial (Coord k n d) (GenericField k n d)) :=
  Ideal.span (Set.range MvPolynomial.X)

noncomputable def saturated (k : ℕ) (n d : Fin k → ℕ)
    (J : Ideal (MvPolynomial (Coord k n d) (GenericField k n d))) :
    Ideal (MvPolynomial (Coord k n d) (GenericField k n d)) :=
  ⨆ e : ℕ, (J : Submodule _ _).colon
    ((originIdeal k n d ^ e : Ideal _) : Set _)

noncomputable def weight (k : ℕ) (n d : Fin k → ℕ)
    (α : Coord k n d) : ℕ :=
  ∏ j : Fin k,
    Fintype.card {f : Fin (d j) → Fin (n j) //
      (Finset.univ.val.map f : Multiset (Fin (n j))) = (α j : Multiset _)}

abbrev Form (k : ℕ) (n d : Fin k → ℕ) :=
  Coord k n d → Coord k n d → ℝ

def PositiveDefinite (k : ℕ) (n d : Fin k → ℕ)
    (Q : Form k n d) : Prop :=
  (∀ α β, Q α β = Q β α) ∧
    ∀ v : Coord k n d → ℝ, v ≠ 0 →
      0 < ∑ α, ∑ β, v α * Q α β * v β

noncomputable def Frobenius (k : ℕ) (n d : Fin k → ℕ) : Form k n d :=
  fun α β => if α = β then (weight k n d α : ℝ) else 0

noncomputable def objective (k : ℕ) (n d : Fin k → ℕ)
    (Q : Form k n d) :
    MvPolynomial (Coord k n d) (GenericField k n d) :=
  ∑ α, ∑ β,
    MvPolynomial.C
      (algebraMap ℂ (GenericField k n d) (Q α β : ℂ)) *
      (MvPolynomial.C (genericData k n d α) - MvPolynomial.X α) *
      (MvPolynomial.C (genericData k n d β) - MvPolynomial.X β)

abbrev Ambient (k : ℕ) (n d : Fin k → ℕ) :=
  MvPolynomial (Coord k n d) (GenericField k n d)

def codim (k : ℕ) (n d : Fin k → ℕ) : ℕ :=
  Fintype.card (Coord k n d) - (1 + ∑ j : Fin k, (n j - 1))

noncomputable def criticalMinor (k : ℕ) (n d : Fin k → ℕ)
    (Q : Form k n d)
    (rows : Fin (codim k n d) → Ambient k n d)
    (columns : Option (Fin (codim k n d)) ↪ Coord k n d) : Ambient k n d :=
  Matrix.det
    (fun (r c : Option (Fin (codim k n d))) =>
      MvPolynomial.pderiv (columns c)
        (match r with
         | none => objective k n d Q
         | some i => rows i))

noncomputable def criticalIdeal (k : ℕ) (n d : Fin k → ℕ)
    (Q : Form k n d) : Ideal (Ambient k n d) :=
  coneIdeal k n d (GenericField k n d) ⊔
    Ideal.span
      {p | ∃ (rows : Fin (codim k n d) → Ambient k n d)
                 (columns : Option (Fin (codim k n d)) ↪ Coord k n d),
          (∀ i, rows i ∈ coneIdeal k n d (GenericField k n d)) ∧
            p = criticalMinor k n d Q rows columns}

abbrev CriticalScheme (k : ℕ) (n d : Fin k → ℕ)
    (Q : Form k n d) :=
  Ambient k n d ⧸ saturated k n d (criticalIdeal k n d Q)

def GenericFinite (k : ℕ) (n d : Fin k → ℕ)
    (Q : Form k n d) : Prop :=
  FiniteDimensional (GenericField k n d) (CriticalScheme k n d Q)

noncomputable def EDDegree (k : ℕ) (n d : Fin k → ℕ)
    (Q : Form k n d) : ℕ :=
  Module.finrank (GenericField k n d) (CriticalScheme k n d Q)

/-- Exact global Frobenius-minimality assertion for every admissible format and
positive definite real metric. Genericity belongs to the datum, represented
by the fraction field of its independent complex coordinate variables. -/
def Claim : Prop :=
  ∀ (k : ℕ), 1 ≤ k →
    ∀ (n d : Fin k → ℕ),
      (∀ j, 2 ≤ n j ∧ 1 ≤ d j) →
      3 ≤ ∑ j : Fin k, d j →
      ∀ (Q : Form k n d), PositiveDefinite k n d Q →
        GenericFinite k n d Q ∧
        GenericFinite k n d (Frobenius k n d) ∧
        EDDegree k n d (Frobenius k n d) ≤ EDDegree k n d Q

end NLA.Statements.Shared.TR17Geometry
