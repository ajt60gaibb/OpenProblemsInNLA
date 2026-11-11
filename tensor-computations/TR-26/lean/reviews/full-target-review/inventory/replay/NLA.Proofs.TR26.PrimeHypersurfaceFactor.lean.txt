import NLA.Proofs.TR26.FiniteJetFactorLemmas
import Mathlib.RingTheory.Nullstellensatz

/-! A prime image with a deleted-hypersurface lower bound determines one
irreducible nonisotropic factor. Multiplicity in the original discriminant is
a separate obligation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
universe u
namespace NLA.Proofs.TR26

theorem irreducible_dvd_of_vanishing_away_hypersurface
    {ι : Type u} [Finite ι] (P E f : MvPolynomial ι ℂ)
    (hP : Irreducible P) (hPE : ¬ P ∣ E)
    (hE0 : MvPolynomial.eval (0 : ι → ℂ) E = 0)
    (hf : ∀ x : ι → ℂ, x ≠ 0 → MvPolynomial.eval x P = 0 →
      MvPolynomial.eval x E ≠ 0 → MvPolynomial.eval x f = 0) : P ∣ f := by
  have hvan : f * E ∈ MvPolynomial.vanishingIdeal ℂ
      (MvPolynomial.zeroLocus ℂ (Ideal.span {P})) := by
    intro x hx
    have hxP : MvPolynomial.eval x P = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using hx P (Ideal.subset_span (Set.mem_singleton P))
    change MvPolynomial.eval x (f * E) = 0
    rw [map_mul]
    by_cases hx0 : x = 0
    · rw [hx0, hE0, mul_zero]
    by_cases hxE : MvPolynomial.eval x E = 0
    · rw [hxE, mul_zero]
    rw [hf x hx0 hxP hxE, zero_mul]
  have hprime : (Ideal.span {P}).IsPrime := Ideal.isPrime_span_singleton_of_prime hP.prime
  have hmem : f * E ∈ Ideal.span {P} := by
    rw [← hprime.radical, ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
    exact hvan
  exact (hP.prime.dvd_or_dvd (Ideal.mem_span_singleton.mp hmem)).resolve_right hPE

theorem vanishingIdeal_eq_span_irreducible_of_deleted_bound
    {ι : Type u} [Finite ι] (S : Set (ι → ℂ)) (P E : MvPolynomial ι ℂ)
    (hP : Irreducible P) (hPE : ¬ P ∣ E)
    (hE0 : MvPolynomial.eval (0 : ι → ℂ) E = 0)
    (hPI : P ∈ MvPolynomial.vanishingIdeal ℂ S)
    (hlower : ∀ x : ι → ℂ, x ≠ 0 → MvPolynomial.eval x P = 0 →
      MvPolynomial.eval x E ≠ 0 → x ∈ S) :
    MvPolynomial.vanishingIdeal ℂ S = Ideal.span {P} := by
  apply le_antisymm
  · intro f hf
    apply Ideal.mem_span_singleton.mpr
    apply irreducible_dvd_of_vanishing_away_hypersurface P E f hP hPE hE0
    intro x hx hxP hxE
    exact hf x (hlower x hx hxP hxE)
  · apply Ideal.span_le.mpr
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact hPI

theorem exists_unique_nonisotropic_irreducible_factor
    {ι : Type u} [Finite ι] (S : Set (ι → ℂ)) (F E : MvPolynomial ι ℂ)
    (hF0 : F ≠ 0) (hprime : (MvPolynomial.vanishingIdeal ℂ S).IsPrime)
    (hFI : F ∈ MvPolynomial.vanishingIdeal ℂ S)
    (hEI : E ∉ MvPolynomial.vanishingIdeal ℂ S)
    (hE0 : MvPolynomial.eval (0 : ι → ℂ) E = 0)
    (hlower : ∀ x : ι → ℂ, x ≠ 0 → MvPolynomial.eval x F = 0 →
      MvPolynomial.eval x E ≠ 0 → x ∈ S) :
    ∃ P : MvPolynomial ι ℂ, Irreducible P ∧ P ∣ F ∧ ¬ P ∣ E ∧
      MvPolynomial.vanishingIdeal ℂ S = Ideal.span {P} ∧
      ∀ Q : MvPolynomial ι ℂ, Irreducible Q → Q ∣ F → ¬ Q ∣ E → Associated P Q := by
  obtain ⟨P, hP, hPF, hPI⟩ := exists_irreducible_factor_mem_primeIdeal _ hprime F hF0 hFI
  have hPE : ¬ P ∣ E := by
    rintro ⟨R, hR⟩
    apply hEI
    rw [hR]
    exact Ideal.mul_mem_right _ _ hPI
  have hbound : ∀ Q : MvPolynomial ι ℂ, Q ∣ F →
      ∀ x : ι → ℂ, x ≠ 0 → MvPolynomial.eval x Q = 0 →
        MvPolynomial.eval x E ≠ 0 → x ∈ S := by
    rintro Q ⟨R, hR⟩ x hx hxQ hxE
    apply hlower x hx _ hxE
    rw [hR, map_mul, hxQ, zero_mul]
  refine ⟨P, hP, hPF, hPE,
    vanishingIdeal_eq_span_irreducible_of_deleted_bound S P E hP hPE hE0 hPI (hbound P hPF), ?_⟩
  intro Q hQ hQF hQE
  have hQP : Q ∣ P := irreducible_dvd_of_vanishing_away_hypersurface Q E P hQ hQE hE0
    (fun x hx hxQ hxE => hPI x (hbound Q hQF x hx hxQ hxE))
  exact (hQ.associated_of_dvd hP hQP).symm

#assert_trust kernel irreducible_dvd_of_vanishing_away_hypersurface
#assert_trust kernel vanishingIdeal_eq_span_irreducible_of_deleted_bound
#assert_trust kernel exists_unique_nonisotropic_irreducible_factor
#print axioms exists_unique_nonisotropic_irreducible_factor
end NLA.Proofs.TR26
