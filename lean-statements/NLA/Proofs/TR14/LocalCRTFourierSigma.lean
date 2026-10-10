import NLA.Proofs.TR14.LocalCRTMoments
import NLA.Proofs.TR14.FrobeniusMinimal

/-!
The exact dependent-root/local-Fourier node formula for every zero-based
Hankel tensor coordinate in a normalized monic chart. The numerical node
count and frozen SymmetricWidth construction are separate gates.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open NLA.Statements.TR14 Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- A node remembers both its distinct root and its exact local Fourier
character index; repeated roots increase the size of the second fiber. -/
abbrev LocalCRTFourierNode (m : ℕ) (g : Polynomial ℂ) :=
  Σ α : LocalRootIndex g,
    Fin (localFourierCount m (localRootMultiplicity g α))

/-- Exact scalar of one local Fourier node, with the inverse character. -/
def localCRTFourierCoefficient (m : ℕ) (g : Polynomial ℂ)
    (ζ : LocalRootIndex g → ℂ)
    (node : LocalCRTFourierNode m g) : ℂ :=
  (localFourierCount m (localRootMultiplicity g node.1) : ℂ)⁻¹ *
    (((ζ node.1) ^ node.2.val) ^ (localRootMultiplicity g node.1 - 1))⁻¹

/-- One exact zero-based mode vector, shared across every tensor mode. -/
def localCRTFourierVector (m n : ℕ) (g : Polynomial ℂ)
    (w : ∀ α : LocalRootIndex g,
      LocalTruncated (localRootMultiplicity g α))
    (ζ : LocalRootIndex g → ℂ)
    (node : LocalCRTFourierNode m g) : Fin n → ℂ :=
  localModeFourierVector m n (localRootMultiplicity g node.1)
    (localRootMultiplicity_pos g node.1) node.1.val
    (w node.1) (ζ node.1) node.2

/-- Under actual local Frobenius in every CRT factor, all local Fourier
decompositions assemble into one exact dependent-sum tensor formula. -/
theorem localCRT_fourier_sigma_of_local_frobenius {m n : ℕ}
    (hm : 3 ≤ m) (hn : 2 ≤ n)
    (h : Fin (m * (n - 1) + 1) → ℂ) (g : Polynomial ℂ)
    (hg : g.Monic) (hrD : g.natDegree ≤ m * (n - 1))
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hLocal : ∀ α : LocalRootIndex g,
      ∀ a : LocalTruncated (localRootMultiplicity g α),
        (∀ b : LocalTruncated (localRootMultiplicity g α),
          localCRTComponent g hg (quotientMomentFunctional h g hg hrD) α
            (a * b) = 0) → a = 0) :
    ∃ w : ∀ α : LocalRootIndex g,
        LocalTruncated (localRootMultiplicity g α),
    ∃ ζ : LocalRootIndex g → ℂ,
      (∀ α : LocalRootIndex g,
        IsPrimitiveRoot (ζ α) (localFourierCount m (localRootMultiplicity g α))) ∧
      (∀ α : LocalRootIndex g,
        (w α) ^ m = localFrobeniusElement
          (localRootMultiplicity g α) (localRootMultiplicity_pos g α)
          (localCRTComponent g hg (quotientMomentFunctional h g hg hrD) α)) ∧
      ∀ i : Fin m → Fin n,
        Hankel h i = ∑ node : LocalCRTFourierNode m g,
          localCRTFourierCoefficient m g ζ node *
            ∏ k : Fin m, localCRTFourierVector m n g w ζ node (i k) := by
  classical
  have hOne (α : LocalRootIndex g) :=
    local_fourier_mode_coordinates m n (localRootMultiplicity g α)
      hm hn (localRootMultiplicity_pos g α) α.val
      (localCRTComponent g hg (quotientMomentFunctional h g hg hrD) α)
      (hLocal α)
  choose w hw using hOne
  choose ζ hζ using hw
  refine ⟨w, ζ, (fun α => (hζ α).1), (fun α => (hζ α).2.1), ?_⟩
  intro i
  change h (HankelIndex i) = _
  rw [localCRT_moments_of_apolar h g hg hrD hAp (HankelIndex i)]
  have hpow :
      (∑ α : LocalRootIndex g,
        localCRTComponent g hg (quotientMomentFunctional h g hg hrD) α
          ((algebraMap ℂ (LocalTruncated (localRootMultiplicity g α)) α.val +
            localRoot (localRootMultiplicity g α)) ^ (HankelIndex i).val)) =
      (∑ α : LocalRootIndex g,
        localCRTComponent g hg (quotientMomentFunctional h g hg hrD) α
          (∏ k : Fin m,
            (algebraMap ℂ (LocalTruncated (localRootMultiplicity g α)) α.val +
              localRoot (localRootMultiplicity g α)) ^ (i k).val)) := by
    apply Finset.sum_congr rfl
    intro α _
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hpow]
  calc
    (∑ α : LocalRootIndex g,
        localCRTComponent g hg (quotientMomentFunctional h g hg hrD) α
          (∏ k : Fin m,
            (algebraMap ℂ (LocalTruncated (localRootMultiplicity g α)) α.val +
              localRoot (localRootMultiplicity g α)) ^ (i k).val)) =
      ∑ α : LocalRootIndex g,
        ∑ j : Fin (localFourierCount m (localRootMultiplicity g α)),
          localCRTFourierCoefficient m g ζ ⟨α, j⟩ *
            ∏ k : Fin m,
              localCRTFourierVector m n g w ζ ⟨α, j⟩ (i k) := by
        apply Finset.sum_congr rfl
        intro α _
        simpa only [localCRTFourierCoefficient, localCRTFourierVector] using
          (hζ α).2.2 i
    _ = ∑ node : LocalCRTFourierNode m g,
          localCRTFourierCoefficient m g ζ node *
            ∏ k : Fin m, localCRTFourierVector m n g w ζ node (i k) := by
      rw [Fintype.sum_sigma]

/-- The local Frobenius premise is discharged from a nonzero least-degree
apolar polynomial and the audited global quotient Frobenius theorem. -/
theorem localCRT_fourier_sigma_of_minimal {m n : ℕ}
    (hm : 3 ≤ m) (hn : 2 ≤ n)
    (h : Fin (m * (n - 1) + 1) → ℂ) (hh : h ≠ 0)
    (g : Polynomial ℂ) (hg : g.Monic) (hrPos : 1 ≤ g.natDegree)
    (hrD : g.natDegree ≤ m * (n - 1))
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ m * (n - 1), d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ, IsApolar h d hd b → b = 0) :
    ∃ w : ∀ α : LocalRootIndex g,
        LocalTruncated (localRootMultiplicity g α),
    ∃ ζ : LocalRootIndex g → ℂ,
      (∀ α : LocalRootIndex g,
        IsPrimitiveRoot (ζ α) (localFourierCount m (localRootMultiplicity g α))) ∧
      (∀ α : LocalRootIndex g,
        (w α) ^ m = localFrobeniusElement
          (localRootMultiplicity g α) (localRootMultiplicity_pos g α)
          (localCRTComponent g hg (quotientMomentFunctional h g hg hrD) α)) ∧
      ∀ i : Fin m → Fin n,
        Hankel h i = ∑ node : LocalCRTFourierNode m g,
          localCRTFourierCoefficient m g ζ node *
            ∏ k : Fin m, localCRTFourierVector m n g w ζ node (i k) := by
  have hGF := quotientMomentFunctional_frobenius h hh g hg hrPos hrD hAp hmin
  apply localCRT_fourier_sigma_of_local_frobenius hm hn h g hg hrD hAp
  intro α
  exact localCRTComponent_frobenius g hg
    (quotientMomentFunctional h g hg hrD) hGF α

#assert_trust kernel LocalCRTFourierNode
#assert_trust kernel localCRTFourierCoefficient
#assert_trust kernel localCRTFourierVector
#assert_trust kernel localCRT_fourier_sigma_of_local_frobenius
#assert_trust kernel localCRT_fourier_sigma_of_minimal
#print axioms localCRT_fourier_sigma_of_minimal

end
end NLA.Proofs.TR14
