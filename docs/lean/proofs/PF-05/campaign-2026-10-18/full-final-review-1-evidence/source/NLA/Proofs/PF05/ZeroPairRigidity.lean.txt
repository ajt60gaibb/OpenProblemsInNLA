import NLA.Proofs.PF05.ZeroAlternative
import NLA.Proofs.PF05.ZeroDirection

/-! Complete forward PF-05 implication when an actual nonzero orthogonal
pair is present. Other zero, singular and repeated factors remain allowed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05
noncomputable section

@[simp] theorem zeroCanonicalPrimal_identity (A : Sym2) (hA : Symmetric A) :
    zeroCanonicalPrimal 0 0 1 A = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zeroCanonicalPrimal, hA 1 0]
@[simp] theorem zeroCanonicalDual_identity (B : Sym2) (hB : Symmetric B) :
    zeroCanonicalDual 0 0 1 B = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zeroCanonicalDual, hB 1 0]

/-- The displayed canonical maps produce a genuinely nonscalar feasible
straight direction whenever their three direction parameters are nonzero. -/
theorem zeroCanonical_explicit_nonscalar {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → Sym2) (B : Fin q → Sym2)
    (hfact : Factorization M A B) (hrank : M.rank = 3)
    (α β γ : ℝ) (hγ : γ ≠ 0)
    (hAt : ∀ i, PositiveSemidefinite (zeroCanonicalPrimal α β γ (A i)))
    (hBt : ∀ j, PositiveSemidefinite (zeroCanonicalDual α β γ (B j)))
    (hnontrivial : ¬ (γ ^ 2 = 1 ∧ α = 0 ∧ β = 0)) :
    FeasibleDirection A (fun i => zeroPrimalDirection α β γ (A i))
      B (fun j => zeroDualDirection α β γ (B j)) ∧
    ¬ ∃ d : ℝ, (∀ i, zeroPrimalDirection α β γ (A i) = d • A i) ∧
      (∀ j, zeroDualDirection α β γ (B j) = (-d) • B j) := by
  refine ⟨zeroDirection_feasible α β γ hγ A B hfact.1 hfact.2.1 hAt hBt, ?_⟩
  rintro ⟨d, hdA, _⟩
  exact hnontrivial (zeroPrimalDirection_scalar_parameters M A B hfact hrank α β γ d hdA)

/-- Forward uniqueness for a normalized actual P,Q pair. Every alternative
is normalized and reduced by actual congruences, rather than assumed to
have the canonical map. -/
theorem rigid_normalized_zero_pair_unique {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → Sym2) (B : Fin q → Sym2)
    (hfact : Factorization M A B) (hrank : M.rank = 3)
    (i₀ : Fin p) (j₀ : Fin q)
    (hA : A i₀ = !![1,0;0,0]) (hB : B j₀ = !![0,0;0,1])
    (hrigid : InfinitesimallyRigid A B) : UniqueUpToCongruence M A B := by
  intro At Bt ht
  obtain ⟨S, α, β, γ, hS, hγ, hAt, hBt⟩ :=
    zeroAlternative_normal_form M A At B Bt hfact ht hrank i₀ j₀ hA hB
  have hAltA (i : Fin p) : PositiveSemidefinite (zeroCanonicalPrimal α β γ (A i)) := by
    rw [← hAt i]
    exact primalCongruence_psd S _ (ht.1 i)
  have hAltB (j : Fin q) : PositiveSemidefinite (zeroCanonicalDual α β γ (B j)) := by
    rw [← hBt j]
    exact dualCongruence_psd S _ (ht.2.1 j)
  obtain ⟨hs, hα, hβ⟩ := rigid_zeroCanonical_parameters M A B hfact hrank
    α β γ (ne_of_gt hγ) hAltA hAltB hrigid
  have hγ1 : γ = 1 := by nlinarith
  have hreverse : Congruent At A Bt B := by
    refine ⟨S, hS, ?_, ?_⟩
    · intro i
      have hx := hAt i
      rw [hα, hβ, hγ1, zeroCanonicalPrimal_identity (A i) (hfact.1 i).1] at hx
      exact hx.symm
    · intro j
      have hx := hBt j
      rw [hα, hβ, hγ1, zeroCanonicalDual_identity (B j) (hfact.2.1 j).1] at hx
      exact hx.symm
  change Congruent A At B Bt
  exact congruent_symm hreverse

/-- Complete forward implication in the actual nonzero-zero-pair branch,
with the original factors, indices and coordinate system restored. -/
theorem zero_pair_rigid_implies_unique {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A : Fin p → Sym2) (B : Fin q → Sym2)
    (hfact : Factorization M A B) (hrank : M.rank = 3)
    (i₀ : Fin p) (j₀ : Fin q) (hA0 : A i₀ ≠ 0) (hB0 : B j₀ ≠ 0)
    (hzero : M i₀ j₀ = 0) (hrigid : InfinitesimallyRigid A B) :
    UniqueUpToCongruence M A B := by
  have htrace : Matrix.trace (A i₀ * B j₀) = 0 := (hfact.2.2 i₀ j₀).symm.trans hzero
  obtain ⟨S, hS, hP, hQ⟩ := normalize_nonzero_zero_pair (A i₀) (B j₀)
    (hfact.1 i₀) (hfact.2.1 j₀) hA0 hB0 htrace
  let As := fun i => primalCongruence S (A i)
  let Bs := fun j => dualCongruence S (B j)
  have hfs : Factorization M As Bs := factorization_congruence M A B hfact S hS
  have hrs : InfinitesimallyRigid As Bs := infinitesimallyRigid_congruence A B S hS hrigid
  have hus := rigid_normalized_zero_pair_unique M As Bs hfs hrank i₀ j₀ hP hQ hrs
  intro At Bt ht
  let Ats := fun i => primalCongruence S (At i)
  let Bts := fun j => dualCongruence S (Bt j)
  have hfts : Factorization M Ats Bts := factorization_congruence M At Bt ht S hS
  have hmid : Congruent As Ats Bs Bts := hus Ats Bts hfts
  have hbase : Congruent A As B Bs := ⟨S, hS, fun _ => rfl, fun _ => rfl⟩
  have halt : Congruent At Ats Bt Bts := ⟨S, hS, fun _ => rfl, fun _ => rfl⟩
  change Congruent A At B Bt
  exact congruent_trans (congruent_trans hbase hmid) (congruent_symm halt)

#assert_trust kernel zeroCanonical_explicit_nonscalar
#assert_trust kernel rigid_normalized_zero_pair_unique
#assert_trust kernel zero_pair_rigid_implies_unique
#print axioms zeroCanonical_explicit_nonscalar
#print axioms zero_pair_rigid_implies_unique
end
end NLA.Proofs.PF05
