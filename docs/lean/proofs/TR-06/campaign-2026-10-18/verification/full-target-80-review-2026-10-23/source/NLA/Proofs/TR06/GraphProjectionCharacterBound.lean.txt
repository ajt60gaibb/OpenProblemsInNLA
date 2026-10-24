/-
Copyright (c) 2026. Released under Apache 2.0 license.
A single actual character bound for each fixed normalized-graph row projection.
-/
import NLA.Proofs.TR06.GraphProjectionLinear
import NLA.TR06.QuasiFiniteCharacters

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option leancert.trust "kernel"
noncomputable section
open scoped Classical
namespace NLA.Proofs.TR06.GraphProjection
attribute [local instance] RingHom.ker_isPrime

/-- The retained uniform algebraic character bound, with the varying target
base action explicitly constructed from the actual projected coordinate value. -/
theorem exists_uniform_aeval_character_finset_bound
    {S : Type*} [CommRing S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
    {k : ℕ} (f : Fin k → S) :
    ∃ B : ℕ, ∀ (x : Fin k → ℂ) (q : Finset (S →ₐ[ℂ] ℂ)),
      (∀ χ ∈ q, ∀ j, χ (f j) = x j) →
      (∀ χ ∈ q, (MvPolynomial.aeval f : MvPolynomial (Fin k) ℂ →ₐ[ℂ] S).toRingHom.QuasiFiniteAt
        (RingHom.ker χ.toRingHom)) → q.card ≤ B := by
  classical
  let R := MvPolynomial (Fin k) ℂ
  let φ : R →ₐ[ℂ] S := MvPolynomial.aeval f
  let : Algebra R S := φ.toRingHom.toAlgebra
  let : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
  let : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType ℂ R S
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  obtain ⟨B,hB⟩ := NLA.TR06.Proposed.uniform_quasiFinite_character_bound R S ℂ
  refine ⟨B,?_⟩
  intro x q hval hqf
  let ψ : R →ₐ[ℂ] ℂ := MvPolynomial.aeval x
  let aK : Algebra R ℂ := ψ.toRingHom.toAlgebra
  let : Algebra R ℂ := aK
  have hcomm (χ : {χ // χ ∈ q}) (P : R) : χ.val (φ P) = ψ P := by
    have hEq : χ.val.comp φ = ψ := by
      ext j
      simpa only [φ,ψ,AlgHom.comp_apply,MvPolynomial.aeval_X] using hval χ.val χ.property j
    exact AlgHom.congr_fun hEq P
  let lift : {χ // χ ∈ q} → (S →ₐ[R] ℂ) := fun χ =>
    { χ.val.toRingHom with commutes' := fun P => hcomm χ P }
  have hinj : Function.Injective lift := by
    intro χ χ' h
    apply Subtype.ext
    ext a
    exact AlgHom.congr_fun h a
  let qR : Finset (S →ₐ[R] ℂ) := q.attach.image lift
  have hqR : ∀ χ ∈ qR, Algebra.QuasiFiniteAt R (NLA.TR06.Proposed.characterPrime χ).asIdeal := by
    intro χ hχ
    obtain ⟨χ',_hχ',rfl⟩ := Finset.mem_image.mp hχ
    exact hqf χ'.val χ'.property
  have hc : qR.card = q.card := by
    dsimp only [qR]
    rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
  rw [← hc]
  exact hB aK qR hqR

/-- Arbitrary finite indexed injective character assignments have the same
bound; no cardinality convention for infinite sets is used. -/
theorem exists_uniform_aeval_character_family_bound
    {S : Type*} [CommRing S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
    {k : ℕ} (f : Fin k → S) :
    ∃ B : ℕ, ∀ (x : Fin k → ℂ) (ι : Type*) [Fintype ι]
      (χ : ι → S →ₐ[ℂ] ℂ), Function.Injective χ →
      (∀ i j, χ i (f j) = x j) →
      (∀ i, (MvPolynomial.aeval f : MvPolynomial (Fin k) ℂ →ₐ[ℂ] S).toRingHom.QuasiFiniteAt
        (RingHom.ker (χ i).toRingHom)) → Fintype.card ι ≤ B := by
  classical
  obtain ⟨B,hB⟩ := exists_uniform_aeval_character_finset_bound f
  refine ⟨B,?_⟩
  intro x ι _ χ hinj hval hqf
  have h := hB x (Finset.univ.image χ)
    (by intro a ha; obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp ha; exact hval i)
    (by intro a ha; obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp ha; exact hqf i)
  simpa only [Finset.card_image_of_injective _ hinj,Finset.card_univ] using h

open NLA.TR06 NLA.TR06.Segre GraphAlgebra

/-- For each actual pivot pattern and fixed real row map, one bound works for
every projected real value and every finite injective family of actual complex
source characters at quasi-finite kernels. -/
theorem exists_uniform_row_character_family_bound
    {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}
    (q₀ : Fin r → TensorIndex d n) (rows : Fin k → OutputCoordinate d n r → ℝ) :
    ∃ B : ℕ, ∀ (x : Fin k → ℝ) (ι : Type*) [Fintype ι]
      (χ : ι → Source q₀ →ₐ[ℂ] ℂ), Function.Injective χ →
      (∀ i j, χ i (rowProjectionCoordinate q₀ rows j) = (x j : ℂ)) →
      (∀ i, (rowProjectionHom q₀ rows).toRingHom.QuasiFiniteAt
        (RingHom.ker (χ i).toRingHom)) → Fintype.card ι ≤ B := by
  obtain ⟨B,hB⟩ := exists_uniform_aeval_character_family_bound (rowProjectionCoordinate q₀ rows)
  exact ⟨B,fun x ι _ χ hi hv hq => hB (fun j => (x j : ℂ)) ι χ hi hv hq⟩

#print axioms exists_uniform_aeval_character_finset_bound
#print axioms exists_uniform_aeval_character_family_bound
#print axioms exists_uniform_row_character_family_bound
#assert_trust kernel exists_uniform_aeval_character_finset_bound
#assert_trust kernel exists_uniform_aeval_character_family_bound
#assert_trust kernel exists_uniform_row_character_family_bound
end NLA.Proofs.TR06.GraphProjection
